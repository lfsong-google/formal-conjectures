/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 289

*References:*
 - [erdosproblems.com/289](https://www.erdosproblems.com/289)
 - [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial
    number theory (1980).
-/

open Filter Finset

namespace Erdos289

/-- Is it true that, for all sufficiently large $k$, there exist finite intervals
$I_1, \dotsc, I_k \subset \mathbb{N}$, distinct, not overlapping or adjacent, with
$|I_i| \geq 2$ for $1 \leq i \leq k$ such that
$$
1 = \sum_{i=1}^k \sum_{n \in I_i} \frac{1}{n}?
$$
Here two intervals are adjacent if their union is again an interval, so any two of the
$I_i$ must be separated by at least one integer.
-/
def w_Icc (a b : ℕ) : ℚ := ∑ n ∈ Finset.Icc a b, (n⁻¹ : ℚ)

def w_pkt (t : ℕ) : ℚ :=
  w_Icc (2 * t - 2) (2 * t - 1) + w_Icc (2 * t + 1) (2 * t + 2) +
  w_Icc (3 * t - 2) (3 * t + 2) + w_Icc (6 * t - 2) (6 * t + 2)

def pellAnchor : Fin 4 → ℕ × ℕ := ![(2, 3), (14, 15), (84, 85), (492, 493)]
def ulgs_p_idx (m j : ℕ) : ℕ := 2 ^ m * (2 * j + 1) - 1

def ulgs_s_of (B p : ℕ) : ℕ :=
  1189 * (2 * padicValNat 2 (p + 1) + 1) * 2 ^ (60 * (B + 2) * (p + 1))

def ulgs_J (B r : ℕ) : ℕ × ℕ :=
  let p := r / 3
  let u := r % 3
  let s := ulgs_s_of B p
  if u = 0 then (2 * s, 2 * s + 1)
  else if u = 1 then (3 * s + 1, 3 * s + 2)
  else (6 * s + 2, 6 * s + 4)

theorem packet_switch_interval_extension (A : Fin 4 → ℕ × ℕ)
    (hA_bounds : ∀ i : Fin 4, 2 ≤ (A i).1 ∧ (A i).1 < (A i).2 ∧ (A i).2 ≤ 493)
    (hA_sep : ∀ i j : Fin 4, i ≠ j → (A i).2 + 1 < (A j).1 ∨ (A j).2 + 1 < (A i).1)
    (hA_sum : ∑ i : Fin 4, w_Icc (A i).1 (A i).2 = 1188 / 1189)
    (N : ℕ) (hN : 39651 ≤ N)
    (T : Finset ℕ) (hT_sub : T ⊆ Finset.Icc N ((9 * N) / 8)) (hT_div : ∀ t ∈ T, 3 ∣ t)
    (l : ℕ) (R : Fin l → ℕ × ℕ)
    (hR_bounds : ∀ i : Fin l, 495 ≤ (R i).1 ∧ (R i).1 < (R i).2)
    (hR_sep : ∀ i j : Fin l, i ≠ j → (R i).2 + 1 < (R j).1 ∨ (R j).2 + 1 < (R i).1)
    (hRT_sep : ∀ i : Fin l, ∀ t ∈ T,
      ((R i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (R i).1) ∧
      ((R i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (R i).1) ∧
      ((R i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (R i).1))
    (h_weight : ∑ t ∈ T, w_pkt t + ∑ i : Fin l, w_Icc (R i).1 (R i).2 = 1 / 1189)
    (k : ℕ) (hk_low : 4 + l + 4 * T.card ≤ k) (hk_high : k ≤ 4 + l + 5 * T.card) :
    ∃ I : Fin k → ℕ × ℕ,
      (∀ i, (I i).1 < (I i).2) ∧
      (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
      ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1 :=
by
  have h_band_split : ∀ m : ℕ, 2 ≤ m →
      w_Icc (m - 2) (m + 2) = w_Icc (m - 2) (m - 1) + ((m : ℕ)⁻¹ : ℚ) + w_Icc (m + 1) (m + 2) := by
    intro m hm
    obtain ⟨d, rfl⟩ : ∃ d, m = d + 2 := ⟨m - 2, by omega⟩
    have h1 : d + 2 - 2 = d := by omega
    have h2 : d + 2 - 1 = d + 1 := by omega
    have h3 : d + 2 + 1 = d + 3 := by omega
    have h4 : d + 2 + 2 = d + 4 := by omega
    rw [h1, h2, h3, h4]
    unfold w_Icc
    rw [Finset.sum_Icc_succ_top (by omega : d ≤ d + 3 + 1)]
    rw [Finset.sum_Icc_succ_top (by omega : d ≤ d + 2 + 1)]
    rw [Finset.sum_Icc_succ_top (by omega : d ≤ d + 1 + 1)]
    rw [Finset.sum_Icc_succ_top (by omega : d + 3 ≤ d + 3 + 1)]
    rw [Finset.Icc_self, Finset.sum_singleton]
    ring
  have h_single_pkt : ∀ t : ℕ, 6 ≤ t → ∀ c : ℕ, (c = 4 ∨ c = 5) →
      ∃ P : Fin c → ℕ × ℕ,
        (∀ i : Fin c, (P i).1 < (P i).2) ∧
        (∀ i j : Fin c, i ≠ j → (P i).2 + 1 < (P j).1 ∨ (P j).2 + 1 < (P i).1) ∧
        (∀ i : Fin c,
          (2 * t - 2 ≤ (P i).1 ∧ (P i).2 ≤ 2 * t + 2) ∨
          (3 * t - 2 ≤ (P i).1 ∧ (P i).2 ≤ 3 * t + 2) ∨
          (6 * t - 2 ≤ (P i).1 ∧ (P i).2 ≤ 6 * t + 2)) ∧
        ∑ i : Fin c, w_Icc (P i).1 (P i).2 = w_pkt t := by
    intro t ht c hc
    rcases hc with rfl | rfl
    · let P : Fin 4 → ℕ × ℕ :=
        ![(2 * t - 2, 2 * t - 1), (2 * t + 1, 2 * t + 2), (3 * t - 2, 3 * t + 2), (6 * t - 2, 6 * t + 2)]
      refine ⟨P, ?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [P] <;> omega
      · intro i j hij; fin_cases i <;> fin_cases j <;> simp [P] at hij ⊢ <;> omega
      · intro i; fin_cases i <;> simp [P] <;> omega
      · simp [Fin.sum_univ_four, P, w_pkt, add_assoc]
    · let P : Fin 5 → ℕ × ℕ :=
        ![(2 * t - 2, 2 * t + 2), (3 * t - 2, 3 * t - 1), (3 * t + 1, 3 * t + 2),
          (6 * t - 2, 6 * t - 1), (6 * t + 1, 6 * t + 2)]
      refine ⟨P, ?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [P] <;> omega
      · intro i j hij; fin_cases i <;> fin_cases j <;> simp [P] at hij ⊢ <;> omega
      · intro i; fin_cases i <;> simp [P] <;> omega
      · simp [Fin.sum_univ_five, P]
        have hb2 := h_band_split (2 * t) (by omega)
        have hb3 := h_band_split (3 * t) (by omega)
        have hb6 := h_band_split (6 * t) (by omega)
        have h_inv : ((2 * t : ℕ)⁻¹ : ℚ) = ((3 * t : ℕ)⁻¹ : ℚ) + ((6 * t : ℕ)⁻¹ : ℚ) := by
          push_cast
          have ht0 : (t : ℚ) ≠ 0 := by positivity
          field_simp
          ring
        unfold w_pkt
        linarith
  have h_cross_sep : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ a b : ℕ,
      ((2 * t - 2 ≤ a ∧ b ≤ 2 * t + 2) ∨
       (3 * t - 2 ≤ a ∧ b ≤ 3 * t + 2) ∨
       (6 * t - 2 ≤ a ∧ b ≤ 6 * t + 2)) →
      ((b + 1 < 2 * u - 2 ∨ 2 * u + 3 < a) ∧
       (b + 1 < 3 * u - 2 ∨ 3 * u + 3 < a) ∧
       (b + 1 < 6 * u - 2 ∨ 6 * u + 3 < a)) := by
    intro t ht u hu htu a b h_band
    have ht_mem := Finset.mem_Icc.mp (hT_sub ht)
    have hu_mem := Finset.mem_Icc.mp (hT_sub hu)
    obtain ⟨kt, rfl⟩ := hT_div t ht
    obtain ⟨ku, rfl⟩ := hT_div u hu
    rcases h_band with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have h_ind : ∀ (S : Finset ℕ), S ⊆ T →
      ∀ (b₀ : ℕ) (B : Fin b₀ → ℕ × ℕ),
        (∀ i : Fin b₀, (B i).1 < (B i).2) →
        (∀ i j : Fin b₀, i ≠ j → (B i).2 + 1 < (B j).1 ∨ (B j).2 + 1 < (B i).1) →
        (∀ i : Fin b₀, ∀ t ∈ S,
          ((B i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (B i).1) ∧
          ((B i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (B i).1) ∧
          ((B i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (B i).1)) →
        ∀ (k : ℕ), b₀ + 4 * S.card ≤ k → k ≤ b₀ + 5 * S.card →
          ∃ I : Fin k → ℕ × ℕ,
            (∀ i, (I i).1 < (I i).2) ∧
            (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
            ∑ i : Fin k, w_Icc (I i).1 (I i).2 =
              ∑ i : Fin b₀, w_Icc (B i).1 (B i).2 + ∑ t ∈ S, w_pkt t := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ b₀ B hB_len hB_sep _ k hk1 hk2
      have h_eq : k = b₀ := by simp at hk1 hk2; omega
      subst h_eq
      refine ⟨B, hB_len, hB_sep, by simp⟩
    | @insert t₀ S' ht₀ ih =>
      intro hS_sub b₀ B hB_len hB_sep hBS_sep k hk1 hk2
      have hcard : (insert t₀ S').card = S'.card + 1 := Finset.card_insert_of_notMem ht₀
      rw [hcard] at hk1 hk2
      let c : ℕ := if b₀ + 4 * S'.card + 5 ≤ k then 5 else 4
      have hc : c = 4 ∨ c = 5 := by
        dsimp [c]; split_ifs <;> [right; left] <;> rfl
      have hk1' : (b₀ + c) + 4 * S'.card ≤ k := by
        dsimp [c]; split_ifs <;> omega
      have hk2' : k ≤ (b₀ + c) + 5 * S'.card := by
        dsimp [c]; split_ifs <;> omega
      have ht₀_T : t₀ ∈ T := hS_sub (Finset.mem_insert_self t₀ S')
      have ht₀_ge : 6 ≤ t₀ := by
        have := (Finset.mem_Icc.mp (hT_sub ht₀_T)).1
        omega
      obtain ⟨P, hP_len, hP_sep, hP_band, hP_sum⟩ := h_single_pkt t₀ ht₀_ge c hc
      let B' : Fin (b₀ + c) → ℕ × ℕ := Fin.addCases B P
      have hB'_len : ∀ i : Fin (b₀ + c), (B' i).1 < (B' i).2 := by
        intro i
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
        · simp [B', hB_len i₁]
        · simp [B', hP_len i₂]
      have hB'_sep : ∀ i j : Fin (b₀ + c), i ≠ j → (B' i).2 + 1 < (B' j).1 ∨ (B' j).2 + 1 < (B' i).1 := by
        intro i j
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
          refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
          intro hij
        · simp only [B', Fin.addCases_left]
          exact hB_sep i₁ j₁ (fun h => hij (congrArg (Fin.castAdd c) h))
        · simp only [B', Fin.addCases_left, Fin.addCases_right]
          have h_bs := hBS_sep i₁ t₀ (Finset.mem_insert_self t₀ S')
          have h_pb := hP_band j₂
          rcases h_pb with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
        · simp only [B', Fin.addCases_left, Fin.addCases_right]
          have h_bs := hBS_sep j₁ t₀ (Finset.mem_insert_self t₀ S')
          have h_pb := hP_band i₂
          rcases h_pb with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
        · simp only [B', Fin.addCases_right]
          exact hP_sep i₂ j₂ (fun h => hij (congrArg (Fin.natAdd b₀) h))
      have hB'S'_sep : ∀ i : Fin (b₀ + c), ∀ u ∈ S',
          ((B' i).2 + 1 < 2 * u - 2 ∨ 2 * u + 3 < (B' i).1) ∧
          ((B' i).2 + 1 < 3 * u - 2 ∨ 3 * u + 3 < (B' i).1) ∧
          ((B' i).2 + 1 < 6 * u - 2 ∨ 6 * u + 3 < (B' i).1) := by
        intro i u hu
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
        · simp only [B', Fin.addCases_left]
          exact hBS_sep i₁ u (Finset.mem_insert_of_mem hu)
        · simp only [B', Fin.addCases_right]
          have hu_T : u ∈ T := hS_sub (Finset.mem_insert_of_mem hu)
          have hne : t₀ ≠ u := fun h => ht₀ (h ▸ hu)
          exact h_cross_sep t₀ ht₀_T u hu_T hne (P i₂).1 (P i₂).2 (hP_band i₂)
      have hS'_sub : S' ⊆ T := fun x hx => hS_sub (Finset.mem_insert_of_mem hx)
      obtain ⟨I, hI_len, hI_sep, hI_sum⟩ :=
        ih hS'_sub (b₀ + c) B' hB'_len hB'_sep hB'S'_sep k hk1' hk2'
      refine ⟨I, hI_len, hI_sep, ?_⟩
      have hB'_sum : ∑ i : Fin (b₀ + c), w_Icc (B' i).1 (B' i).2 =
          ∑ i : Fin b₀, w_Icc (B i).1 (B i).2 + w_pkt t₀ := by
        rw [Fin.sum_univ_add]
        simp only [B', Fin.addCases_left, Fin.addCases_right, hP_sum]
      rw [hI_sum, hB'_sum, Finset.sum_insert ht₀]
      ring
  let B₀ : Fin (4 + l) → ℕ × ℕ := Fin.addCases A R
  have hB₀_len : ∀ i : Fin (4 + l), (B₀ i).1 < (B₀ i).2 := by
    intro i
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
    · simp [B₀, (hA_bounds i₁).2.1]
    · simp [B₀, (hR_bounds i₂).2]
  have hB₀_sep : ∀ i j : Fin (4 + l), i ≠ j → (B₀ i).2 + 1 < (B₀ j).1 ∨ (B₀ j).2 + 1 < (B₀ i).1 := by
    intro i j
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
      intro hij
    · simp only [B₀, Fin.addCases_left]
      exact hA_sep i₁ j₁ (fun h => hij (congrArg (Fin.castAdd l) h))
    · simp only [B₀, Fin.addCases_left, Fin.addCases_right]
      have hA := (hA_bounds i₁).2.2
      have hR := (hR_bounds j₂).1
      omega
    · simp only [B₀, Fin.addCases_left, Fin.addCases_right]
      have hA := (hA_bounds j₁).2.2
      have hR := (hR_bounds i₂).1
      omega
    · simp only [B₀, Fin.addCases_right]
      exact hR_sep i₂ j₂ (fun h => hij (congrArg (Fin.natAdd 4) h))
  have hB₀T_sep : ∀ i : Fin (4 + l), ∀ t ∈ T,
      ((B₀ i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (B₀ i).1) ∧
      ((B₀ i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (B₀ i).1) ∧
      ((B₀ i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (B₀ i).1) := by
    intro i t ht
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
    · simp only [B₀, Fin.addCases_left]
      have hA := (hA_bounds i₁).2.2
      have ht_ge := (Finset.mem_Icc.mp (hT_sub ht)).1
      omega
    · simp only [B₀, Fin.addCases_right]
      exact hRT_sep i₂ t ht
  obtain ⟨I, hI_len, hI_sep, hI_sum⟩ :=
    h_ind T (Finset.Subset.refl T) (4 + l) B₀ hB₀_len hB₀_sep hB₀T_sep k hk_low hk_high
  refine ⟨I, hI_len, hI_sep, ?_⟩
  have hB₀_sum : ∑ i : Fin (4 + l), w_Icc (B₀ i).1 (B₀ i).2 =
      1188 / 1189 + ∑ i : Fin l, w_Icc (R i).1 (R i).2 := by
    rw [Fin.sum_univ_add]
    simp only [B₀, Fin.addCases_left, Fin.addCases_right, hA_sum]
  change ∑ i : Fin k, w_Icc (I i).1 (I i).2 = 1
  linarith [hI_sum, hB₀_sum, h_weight]

theorem smooth_sieve_pow_bad_bound : ∃ N_pow : ℕ, 475600 ≤ N_pow ∧ ∀ N ≥ N_pow, ∀ Y : ℕ,
      Y ^ 512 ≤ N ^ 511 → N ^ 511 < (Y + 1) ^ 512 →
      ∃ B_pow : Finset ℕ, B_pow.card ≤ N / 1000 ∧
        ∀ t ∈ Finset.Icc N ((9 * N) / 8), 3 ∣ t →
          (∃ c ∈ ({2, 3, 6} : Finset ℕ), ∃ n ∈ Finset.Icc (c * t - 2) (c * t + 2),
            ∃ p k : ℕ, Nat.Prime p ∧ p ≤ Y ∧ p ^ k ∣ n ∧ Y < p ^ k) →
          t ∈ B_pow :=
by
  refine ⟨49 * 105000 ^ 4, by norm_num, ?_⟩
  intro N hN Y hY1 hY2
  have hN_small : 475600 ≤ N := le_trans (by norm_num : 475600 ≤ 49 * 105000 ^ 4) hN
  let S_c : Finset ℕ := {2, 3, 6}
  let S_d : Finset ℕ := Finset.range 5
  let S_p : Finset ℕ := Finset.Icc 2 (Nat.sqrt (7 * N))
  let S_m : Finset ℕ := Finset.Icc 1 ((7 * N) / (Y + 1))
  let f : ℕ → ℕ → ℕ → ℕ → ℕ := fun c d p m =>
    (p ^ (Nat.log p Y + 1) * m + 2 - d) / c
  let B_pow : Finset ℕ :=
    S_c.biUnion (fun c => S_d.biUnion (fun d => S_p.biUnion (fun p => S_m.image (fun m => f c d p m))))
  refine ⟨B_pow, ?_, ?_⟩
  · have h_card_m : ∀ c d p, (S_m.image (fun m => f c d p m)).card ≤ (7 * N) / (Y + 1) := by
      intro c d p
      exact le_trans Finset.card_image_le (by simp [S_m, Nat.card_Icc])
    have h_card_p : ∀ c d, (S_p.biUnion (fun p => S_m.image (fun m => f c d p m))).card ≤
        Nat.sqrt (7 * N) * ((7 * N) / (Y + 1)) := by
      intro c d
      have h1 := Finset.card_biUnion_le (s := S_p) (t := fun p => S_m.image (fun m => f c d p m))
      have h2 := Finset.sum_le_card_nsmul S_p (fun p => (S_m.image (fun m => f c d p m)).card)
        ((7 * N) / (Y + 1)) (fun p _ => h_card_m c d p)
      have h3 : S_p.card ≤ Nat.sqrt (7 * N) := by simp [S_p, Nat.card_Icc]
      rw [nsmul_eq_mul] at h2
      exact le_trans h1 (le_trans h2 (Nat.mul_le_mul_right _ h3))
    have h_card_d : ∀ c, (S_d.biUnion (fun d => S_p.biUnion (fun p => S_m.image (fun m => f c d p m)))).card ≤
        5 * (Nat.sqrt (7 * N) * ((7 * N) / (Y + 1))) := by
      intro c
      have h1 := Finset.card_biUnion_le (s := S_d) (t := fun d => S_p.biUnion (fun p => S_m.image (fun m => f c d p m)))
      have h2 := Finset.sum_le_card_nsmul S_d _ (Nat.sqrt (7 * N) * ((7 * N) / (Y + 1))) (fun d _ => h_card_p c d)
      have h3 : S_d.card = 5 := by simp [S_d]
      rw [h3, nsmul_eq_mul] at h2
      exact le_trans h1 h2
    have h_card_c : B_pow.card ≤ 15 * Nat.sqrt (7 * N) * ((7 * N) / (Y + 1)) := by
      have h1 := Finset.card_biUnion_le (s := S_c) (t := fun c => S_d.biUnion (fun d => S_p.biUnion (fun p => S_m.image (fun m => f c d p m))))
      have h2 := Finset.sum_le_card_nsmul S_c _ (5 * (Nat.sqrt (7 * N) * ((7 * N) / (Y + 1)))) (fun c _ => h_card_d c)
      have h3 : S_c.card ≤ 3 := by decide
      rw [nsmul_eq_mul] at h2
      have h4 := le_trans h1 (le_trans h2 (Nat.mul_le_mul_right _ h3))
      linarith
    have h_N3_lt : N ^ 3 < (Y + 1) ^ 4 := by
      by_contra h_ge
      push_neg at h_ge
      have h_pow := Nat.pow_le_pow_left h_ge 128
      rw [← pow_mul, ← pow_mul] at h_pow
      have h_384_511 : N ^ (3 * 128) ≤ N ^ 511 := Nat.pow_le_pow_right (by omega : 1 ≤ N) (by norm_num)
      have h_le_Y : N ^ (3 * 128) < (Y + 1) ^ (4 * 128) := lt_of_le_of_lt h_384_511 hY2
      exact not_lt_of_ge h_pow h_le_Y
    have h_sqrt_sq : (Nat.sqrt (7 * N)) ^ 2 ≤ 7 * N := Nat.sqrt_le' (7 * N)
    have h_sqrt_4 : (105000 * Nat.sqrt (7 * N)) ^ 4 ≤ N ^ 3 := by
      calc (105000 * Nat.sqrt (7 * N)) ^ 4
        _ = 105000 ^ 4 * ((Nat.sqrt (7 * N)) ^ 2) ^ 2 := by ring
        _ ≤ 105000 ^ 4 * (7 * N) ^ 2 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left h_sqrt_sq 2
        _ = (49 * 105000 ^ 4) * N ^ 2 := by ring
        _ ≤ N * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) hN
        _ = N ^ 3 := by ring
    clear hN
    have h_4_lt : (105000 * Nat.sqrt (7 * N)) ^ 4 < (Y + 1) ^ 4 := lt_of_le_of_lt h_sqrt_4 h_N3_lt
    have h_Y_gt : 105000 * Nat.sqrt (7 * N) < Y + 1 := by
      by_contra h_le
      push_neg at h_le
      exact not_lt_of_ge (Nat.pow_le_pow_left h_le 4) h_4_lt
    have h_div_le : 15 * Nat.sqrt (7 * N) * ((7 * N) / (Y + 1)) ≤ N / 1000 := by
      have h_mul_div : (105000 * Nat.sqrt (7 * N)) * ((7 * N) / (Y + 1)) ≤ 7 * N := by
        calc (105000 * Nat.sqrt (7 * N)) * ((7 * N) / (Y + 1))
          _ ≤ (Y + 1) * ((7 * N) / (Y + 1)) := Nat.mul_le_mul_right _ (le_of_lt h_Y_gt)
          _ ≤ 7 * N := Nat.mul_div_le (7 * N) (Y + 1)
      have h_rew : 105000 * Nat.sqrt (7 * N) * ((7 * N) / (Y + 1)) =
          7000 * (15 * Nat.sqrt (7 * N) * ((7 * N) / (Y + 1))) := by ring
      rw [h_rew] at h_mul_div
      omega
    exact le_trans h_card_c h_div_le
  · clear hN
    intro t ht _ h_bad
    rcases h_bad with ⟨c, hc, n, hn, p, k, hp, hpY, hpk_n, hY_pk⟩
    have ht_Icc := Finset.mem_Icc.mp ht
    have hn_Icc := Finset.mem_Icc.mp hn
    have hc_cases : c = 2 ∨ c = 3 ∨ c = 6 := by simpa [S_c] using hc
    have hn_bounds : 1 ≤ n ∧ n ≤ 7 * N := by
      rcases hc_cases with rfl | rfl | rfl <;> omega
    set r : ℕ := Nat.log p Y + 1
    have hp_gt1 : 1 < p := hp.one_lt
    have h_pr_gt_Y : Y < p ^ r := Nat.lt_pow_succ_log_self hp_gt1 Y
    have h_log_le : p ^ Nat.log p Y ≤ Y := Nat.pow_log_le_self p (by omega)
    have h_r_le_k : r ≤ k := by
      have h_lt : p ^ Nat.log p Y < p ^ k := lt_of_le_of_lt h_log_le hY_pk
      have : Nat.log p Y < k := (Nat.pow_lt_pow_iff_right hp_gt1).mp h_lt
      omega
    have h_pr_dvd_pk : p ^ r ∣ p ^ k := Nat.pow_dvd_pow p h_r_le_k
    have h_pr_dvd_n : p ^ r ∣ n := dvd_trans h_pr_dvd_pk hpk_n
    rcases h_pr_dvd_n with ⟨m, hm_eq⟩
    have hm_pos : 1 ≤ m := by
      by_contra hm0
      have : m = 0 := by omega
      subst this
      omega
    have hm_le : m ≤ (7 * N) / (Y + 1) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc m * (Y + 1)
        _ ≤ m * p ^ r := Nat.mul_le_mul_left m h_pr_gt_Y
        _ = n := by rw [mul_comm, ← hm_eq]
        _ ≤ 7 * N := hn_bounds.2
    have h_r_ge2 : 2 ≤ r := by
      have : 1 ≤ Nat.log p Y := Nat.log_pos hp_gt1 hpY
      omega
    have hp2_le_n : p ^ 2 ≤ 7 * N := by
      calc p ^ 2
        _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos h_r_ge2
        _ ≤ p ^ r * m := Nat.le_mul_of_pos_right _ hm_pos
        _ = n := hm_eq.symm
        _ ≤ 7 * N := hn_bounds.2
    have hp_sqrt : p ≤ Nat.sqrt (7 * N) := Nat.le_sqrt.mpr (by nlinarith)
    set d : ℕ := n - (c * t - 2)
    have hd_mem : d ∈ S_d := by
      simp only [S_d, Finset.mem_range]
      omega
    have hp_mem : p ∈ S_p := Finset.mem_Icc.mpr ⟨hp.two_le, hp_sqrt⟩
    have hm_mem : m ∈ S_m := Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩
    have hf_eq : f c d p m = t := by
      dsimp [f]
      rw [← hm_eq]
      rcases hc_cases with rfl | rfl | rfl <;> omega
    rw [← hf_eq]
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_biUnion.mpr ⟨d, hd_mem,
      Finset.mem_biUnion.mpr ⟨p, hp_mem, Finset.mem_image.mpr ⟨m, hm_mem, rfl⟩⟩⟩⟩

theorem smooth_sieve_prime_bad_bound : ∃ N_prime : ℕ, 475600 ≤ N_prime ∧ ∀ N ≥ N_prime, ∀ Y : ℕ,
      Y ^ 512 ≤ N ^ 511 → N ^ 511 < (Y + 1) ^ 512 →
      ∃ B_prime : Finset ℕ, B_prime.card ≤ N / 60 ∧
        ∀ t ∈ Finset.Icc N ((9 * N) / 8), 3 ∣ t →
          (∃ c ∈ ({2, 3, 6} : Finset ℕ), ∃ n ∈ Finset.Icc (c * t - 2) (c * t + 2),
            ∃ p : ℕ, Nat.Prime p ∧ Y < p ∧ p ∣ n) →
          t ∈ B_prime :=
by
  have h_s1 : ∀ (N c d p : ℕ), 475600 ≤ N → c ∈ ({2, 3, 6} : Finset ℕ) → Nat.Prime p → 18 < p →
      (((Finset.Icc N ((9 * N) / 8)).filter (fun t => 3 ∣ t)).filter
        (fun t => p ∣ (c * t - 2 + d))).card ≤ N / (24 * p) + 1 := by
    intro N c d p hN hc hp hp18
    let I_N := (Finset.Icc N ((9 * N) / 8)).filter (fun t => 3 ∣ t)
    let F := I_N.filter (fun t => p ∣ (c * t - 2 + d))
    change F.card ≤ N / (24 * p) + 1
    by_cases hF : F.Nonempty
    · let t0 := F.min' hF
      have ht0_mem : t0 ∈ F := Finset.min'_mem F hF
      have ht0_IN : t0 ∈ I_N := (Finset.mem_filter.mp ht0_mem).1
      have ht0_dvd : p ∣ (c * t0 - 2 + d) := (Finset.mem_filter.mp ht0_mem).2
      have ht0_Icc : N ≤ t0 ∧ t0 ≤ (9 * N) / 8 := Finset.mem_Icc.mp (Finset.mem_filter.mp ht0_IN).1
      have ht0_3 : 3 ∣ t0 := (Finset.mem_filter.mp ht0_IN).2
      have hc_cases : c = 2 ∨ c = 3 ∨ c = 6 := by simpa using hc
      let g : ℕ → ℕ := fun t => (t / 3 - t0 / 3) / p
      have h_reconstruct : ∀ t ∈ F, p * g t = t / 3 - t0 / 3 ∧ t = t0 + 3 * (p * g t) ∧ g t < N / (24 * p) + 1 := by
        intro t ht
        have ht_le : t0 ≤ t := Finset.min'_le F t ht
        have ht_IN : t ∈ I_N := (Finset.mem_filter.mp ht).1
        have ht_dvd : p ∣ (c * t - 2 + d) := (Finset.mem_filter.mp ht).2
        have ht_Icc : N ≤ t ∧ t ≤ (9 * N) / 8 := Finset.mem_Icc.mp (Finset.mem_filter.mp ht_IN).1
        have ht_3 : 3 ∣ t := (Finset.mem_filter.mp ht_IN).2
        have h_sub_eq : (c * t - 2 + d) - (c * t0 - 2 + d) = (3 * c) * (t / 3 - t0 / 3) := by
          rcases hc_cases with rfl | rfl | rfl <;> omega
        have h_dvd_sub : p ∣ (c * t - 2 + d) - (c * t0 - 2 + d) := Nat.dvd_sub ht_dvd ht0_dvd
        rw [h_sub_eq] at h_dvd_sub
        have h_not_dvd_3c : ¬ (p ∣ 3 * c) := by
          intro h_div
          have h_pos : 0 < 3 * c := by rcases hc_cases with rfl | rfl | rfl <;> omega
          have h_le : p ≤ 3 * c := Nat.le_of_dvd h_pos h_div
          rcases hc_cases with rfl | rfl | rfl <;> omega
        have h_dvd_quot : p ∣ (t / 3 - t0 / 3) := by
          rcases hp.dvd_mul.mp h_dvd_sub with h1 | h2
          · exact False.elim (h_not_dvd_3c h1)
          · exact h2
        have h_pg : p * g t = t / 3 - t0 / 3 := Nat.mul_div_cancel' h_dvd_quot
        have h_t_eq : t = t0 + 3 * (p * g t) := by
          rw [h_pg]
          omega
        have h_diff_bound : t / 3 - t0 / 3 ≤ N / 24 := by omega
        have h_g_le : g t ≤ N / (24 * p) := by
          dsimp [g]
          rw [← Nat.div_div_eq_div_mul]
          exact Nat.div_le_div_right h_diff_bound
        exact ⟨h_pg, h_t_eq, by omega⟩
      have h_maps : Set.MapsTo g F (Finset.range (N / (24 * p) + 1)) := by
        intro t ht
        rw [Finset.mem_coe, Finset.mem_range]
        exact (h_reconstruct t ht).2.2
      have h_inj : Set.InjOn g F := by
        intro t1 ht1 t2 ht2 h_eq
        have h1 := (h_reconstruct t1 ht1).2.1
        have h2 := (h_reconstruct t2 ht2).2.1
        rw [h1, h2, h_eq]
      have h_card := Finset.card_le_card_of_injOn g h_maps h_inj
      simpa using h_card
    · rw [Finset.not_nonempty_iff_eq_empty] at hF
      rw [hF]
      simp

  have h_s2_1 : ∀ (L A B : ℕ), 2 ^ L ≤ A →
      L * ((Finset.Icc (A + 1) B).filter Nat.Prime).card ≤ 2 * B := by
    intro L A B hA
    let S := (Finset.Icc (A + 1) B).filter Nat.Prime
    have h_low : ∀ p ∈ S, 2 ^ L ≤ p := by
      intro p hp
      have hp_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      omega
    have h_pow_prod : (2 ^ L) ^ S.card ≤ ∏ p ∈ S, p :=
      Finset.pow_card_le_prod S id (2 ^ L) h_low
    have h_sub : S ⊆ (Finset.range (B + 1)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    have h_one_le : ∀ p ∈ (Finset.range (B + 1)).filter Nat.Prime, p ∉ S → 1 ≤ p := by
      intro p hp _
      have hp_prime := (Finset.mem_filter.mp hp).2
      exact hp_prime.one_le
    have h_prod_le : ∏ p ∈ S, p ≤ ∏ p ∈ (Finset.range (B + 1)).filter Nat.Prime, p :=
      Finset.prod_le_prod_of_subset_of_one_le' h_sub h_one_le
    have h_prim : (∏ p ∈ (Finset.range (B + 1)).filter Nat.Prime, p) = primorial B := rfl
    have h_4pow : primorial B ≤ 4 ^ B := primorial_le_4_pow B
    have h_chain : 2 ^ (L * S.card) ≤ 2 ^ (2 * B) := by
      calc 2 ^ (L * S.card) = (2 ^ L) ^ S.card := by rw [pow_mul]
        _ ≤ ∏ p ∈ S, p := h_pow_prod
        _ ≤ primorial B := by rw [← h_prim]; exact h_prod_le
        _ ≤ 4 ^ B := h_4pow
        _ = (2 ^ 2) ^ B := by norm_num
        _ = 2 ^ (2 * B) := by rw [← pow_mul]
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h_chain

  have h_s2_3 : ∀ (N Y L k : ℕ), 1 ≤ L → 2 ^ L ≤ Y →
      ∑ p ∈ (Finset.Icc (2 ^ k * Y + 1) (2 ^ (k + 1) * Y)).filter Nat.Prime, (N / (24 * p)) ≤ N / (6 * L) := by
    intro N Y L k hL hY
    let P_k := (Finset.Icc (2 ^ k * Y + 1) (2 ^ (k + 1) * Y)).filter Nat.Prime
    have hk_pos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    have h2L_pos : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by omega)
    have hA : 2 ^ L ≤ 2 ^ k * Y := le_trans hY (Nat.le_mul_of_pos_left Y hk_pos)
    have h_card : L * P_k.card ≤ 2 * (2 ^ (k + 1) * Y) := h_s2_1 L (2 ^ k * Y) (2 ^ (k + 1) * Y) hA
    have h_term : ∀ p ∈ P_k, N / (24 * p) ≤ N / (24 * (2 ^ k * Y)) := by
      intro p hp
      have hp_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      have h_denom_pos : 0 < 24 * (2 ^ k * Y) := by omega
      have h_denom_le : 24 * (2 ^ k * Y) ≤ 24 * p := by omega
      exact Nat.div_le_div_left h_denom_le h_denom_pos
    have h_sum_le := Finset.sum_le_card_nsmul P_k (fun p => N / (24 * p)) (N / (24 * (2 ^ k * Y))) h_term
    rw [nsmul_eq_mul] at h_sum_le
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h_card_rew : 6 * (L * P_k.card) ≤ 24 * (2 ^ k * Y) := by
      have : 2 * (2 ^ (k + 1) * Y) = 4 * (2 ^ k * Y) := by ring
      omega
    calc (∑ p ∈ P_k, (N / (24 * p))) * (6 * L)
        = (6 * L) * ∑ p ∈ P_k, (N / (24 * p)) := by ring
      _ ≤ (6 * L) * (P_k.card * (N / (24 * (2 ^ k * Y)))) := Nat.mul_le_mul_left (6 * L) h_sum_le
      _ = (6 * (L * P_k.card)) * (N / (24 * (2 ^ k * Y))) := by ring
      _ ≤ (24 * (2 ^ k * Y)) * (N / (24 * (2 ^ k * Y))) := Nat.mul_le_mul_right _ h_card_rew
      _ ≤ N := Nat.mul_div_le N (24 * (2 ^ k * Y))

  have h_s3 : ∀ (N Y : ℕ), 2 ^ 25300 ≤ N → N ^ 511 < (Y + 1) ^ 512 →
      let L := Nat.log 2 Y
      let K := L / 511 + 5
      25200 ≤ L ∧ 18 < Y ∧ 2 ^ L ≤ Y ∧ 7 * N ≤ 2 ^ K * Y ∧
      (Finset.Icc (Y + 1) (7 * N)).filter Nat.Prime ⊆
        (Finset.range K).biUnion (fun k => (Finset.Icc (2 ^ k * Y + 1) (2 ^ (k + 1) * Y)).filter Nat.Prime) := by
    intro N Y hN hY2 L K
    have hN_pos : 1 ≤ N := le_trans (Nat.one_le_pow 25300 2 (by omega)) hN
    have hY_ne0 : Y ≠ 0 := by
      intro hY0
      subst hY0
      have : 1 ≤ N ^ 511 := Nat.one_le_pow 511 N hN_pos
      omega
    have h2L_le_Y : 2 ^ L ≤ Y := Nat.pow_log_le_self 2 hY_ne0
    have hY_lt_2L1 : Y < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 2) Y
    have hL_ge : 25200 ≤ L := by
      by_contra h_lt
      have hL1_le : L + 1 ≤ 25200 := by omega
      have hY1_le : Y + 1 ≤ 2 ^ 25200 :=
        le_trans (by omega : Y + 1 ≤ 2 ^ (L + 1)) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hL1_le)
      have h_pow1 : (Y + 1) ^ 512 ≤ (2 ^ 25200) ^ 512 := Nat.pow_le_pow_left hY1_le 512
      have h_pow2 : (2 ^ 25200) ^ 512 ≤ (2 ^ 25300) ^ 511 := by
        rw [← pow_mul, ← pow_mul]
        exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 25200 * 512 ≤ 25300 * 511)
      have h_pow3 : (2 ^ 25300) ^ 511 ≤ N ^ 511 := Nat.pow_le_pow_left hN 511
      have h_contra : (Y + 1) ^ 512 ≤ N ^ 511 := le_trans h_pow1 (le_trans h_pow2 h_pow3)
      omega
    have h18_lt_Y : 18 < Y := by
      have h32 : 32 ≤ 2 ^ 25200 := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ 25200 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 5 ≤ 25200)
      have h25200_L : 2 ^ 25200 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hL_ge
      have : 32 ≤ Y := le_trans h32 (le_trans h25200_L h2L_le_Y)
      omega
    have h7N_le : 7 * N ≤ 2 ^ K * Y := by
      by_contra h_lt
      have h_le_8N : 2 ^ (K + L) ≤ 2 ^ 3 * N := by
        calc 2 ^ (K + L) = 2 ^ K * 2 ^ L := by rw [pow_add]
          _ ≤ 2 ^ K * Y := Nat.mul_le_mul_left (2 ^ K) h2L_le_Y
          _ ≤ 8 * N := by omega
          _ = 2 ^ 3 * N := by ring
      have h_pow_left : (2 ^ (K + L)) ^ 511 ≤ (2 ^ 3 * N) ^ 511 := Nat.pow_le_pow_left h_le_8N 511
      have h_pow_mid : (2 ^ 3 * N) ^ 511 < 2 ^ 1533 * (Y + 1) ^ 512 := by
        have h_eq : (2 ^ 3 * N) ^ 511 = 2 ^ 1533 * N ^ 511 := by
          rw [mul_pow, ← pow_mul]
        rw [h_eq]
        exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ 1533)).mpr hY2
      have hY1_le : (Y + 1) ^ 512 ≤ (2 ^ (L + 1)) ^ 512 :=
        Nat.pow_le_pow_left (by omega : Y + 1 ≤ 2 ^ (L + 1)) 512
      have h_pow_right : 2 ^ 1533 * (Y + 1) ^ 512 ≤ 2 ^ (1533 + 512 * (L + 1)) := by
        calc 2 ^ 1533 * (Y + 1) ^ 512 ≤ 2 ^ 1533 * (2 ^ (L + 1)) ^ 512 := Nat.mul_le_mul_left _ hY1_le
          _ = 2 ^ 1533 * 2 ^ ((L + 1) * 512) := by rw [← pow_mul]
          _ = 2 ^ (1533 + (L + 1) * 512) := by rw [← pow_add]
          _ = 2 ^ (1533 + 512 * (L + 1)) := by ring_nf
      have h_pow_lt : 2 ^ (511 * (K + L)) < 2 ^ (1533 + 512 * (L + 1)) := by
        calc 2 ^ (511 * (K + L)) = (2 ^ (K + L)) ^ 511 := by rw [mul_comm 511, pow_mul]
          _ < 2 ^ 1533 * (Y + 1) ^ 512 := lt_of_le_of_lt h_pow_left h_pow_mid
          _ ≤ 2 ^ (1533 + 512 * (L + 1)) := h_pow_right
      have h_exp_lt : 511 * (K + L) < 1533 + 512 * (L + 1) :=
        (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h_pow_lt
      dsimp [K] at h_exp_lt
      omega
    have h_cov_ind : ∀ M p : ℕ, Y + 1 ≤ p → p ≤ 2 ^ M * Y →
        ∃ k < M, 2 ^ k * Y + 1 ≤ p ∧ p ≤ 2 ^ (k + 1) * Y := by
      intro M
      induction M with
      | zero =>
        intro p hp1 hp2
        simp at hp2
        omega
      | succ M ih =>
        intro p hp1 hp2
        by_cases hpM : p ≤ 2 ^ M * Y
        · obtain ⟨k, hk, hk1, hk2⟩ := ih p hp1 hpM
          exact ⟨k, by omega, hk1, hk2⟩
        · exact ⟨M, by omega, by omega, hp2⟩
    refine ⟨hL_ge, h18_lt_Y, h2L_le_Y, h7N_le, ?_⟩
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨k, hk, hk1, hk2⟩ := h_cov_ind K p hp.1.1 (le_trans hp.1.2 h7N_le)
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hk1, hk2⟩, hp.2⟩

  have h475600_le : 475600 ≤ 2 ^ 25300 := by
    calc 475600 ≤ 2 ^ 19 := by norm_num
      _ ≤ 2 ^ 25300 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 19 ≤ 25300)
  refine ⟨2 ^ 25300, h475600_le, ?_⟩
  intro N hN Y _ hY2
  have hN_475600 : 475600 ≤ N := le_trans h475600_le hN
  obtain ⟨hL_ge, h18_lt_Y, h2L_le_Y, h7N_le, hP_sub⟩ := h_s3 N Y hN hY2
  clear hN h475600_le
  let L := Nat.log 2 Y
  let K := L / 511 + 5
  let I_N := (Finset.Icc N ((9 * N) / 8)).filter (fun t => 3 ∣ t)
  let P_large := (Finset.Icc (Y + 1) (7 * N)).filter Nat.Prime
  let S_c : Finset ℕ := {2, 3, 6}
  let S_d : Finset ℕ := Finset.range 5
  let F : ℕ → ℕ → ℕ → Finset ℕ := fun c d p => I_N.filter (fun t => p ∣ (c * t - 2 + d))
  let B_prime : Finset ℕ := P_large.biUnion (fun p => S_c.biUnion (fun c => S_d.biUnion (fun d => F c d p)))
  refine ⟨B_prime, ?_, ?_⟩
  · have h_Sc_card : S_c.card ≤ 3 := by
      dsimp [S_c]
      exact le_trans (Finset.card_insert_le _ _)
        (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) (by simp)) 1)
    have h_Sd_card : S_d.card = 5 := Finset.card_range 5
    have h_inner_p : ∀ p ∈ P_large,
        (S_c.biUnion (fun c => S_d.biUnion (fun d => F c d p))).card ≤ 15 * (N / (24 * p) + 1) := by
      intro p hp
      have hp_filter := Finset.mem_filter.mp hp
      have hp_Icc := Finset.mem_Icc.mp hp_filter.1
      have hp_prime := hp_filter.2
      have hp18 : 18 < p := by omega
      have h_inner_c : ∀ c ∈ S_c, (S_d.biUnion (fun d => F c d p)).card ≤ 5 * (N / (24 * p) + 1) := by
        intro c hc
        have h_inner_d : ∀ d ∈ S_d, (F c d p).card ≤ N / (24 * p) + 1 := by
          intro d _
          exact h_s1 N c d p hN_475600 hc hp_prime hp18
        have h_bi := Finset.card_biUnion_le (s := S_d) (t := fun d => F c d p)
        have h_sum := Finset.sum_le_card_nsmul S_d (fun d => (F c d p).card) (N / (24 * p) + 1) h_inner_d
        rw [h_Sd_card, smul_eq_mul] at h_sum
        exact le_trans h_bi h_sum
      have h_bi := Finset.card_biUnion_le (s := S_c) (t := fun c => S_d.biUnion (fun d => F c d p))
      have h_sum := Finset.sum_le_card_nsmul S_c (fun c => (S_d.biUnion (fun d => F c d p)).card) (5 * (N / (24 * p) + 1)) h_inner_c
      rw [smul_eq_mul] at h_sum
      have h_mul : S_c.card * (5 * (N / (24 * p) + 1)) ≤ 15 * (N / (24 * p) + 1) := by
        calc S_c.card * (5 * (N / (24 * p) + 1)) = (S_c.card * 5) * (N / (24 * p) + 1) := by ring
          _ ≤ 15 * (N / (24 * p) + 1) := Nat.mul_le_mul_right _ (by omega)
      exact le_trans h_bi (le_trans h_sum h_mul)
    have h_B_bi := Finset.card_biUnion_le (s := P_large) (t := fun p => S_c.biUnion (fun c => S_d.biUnion (fun d => F c d p)))
    have h_B_sum : ∑ p ∈ P_large, (S_c.biUnion (fun c => S_d.biUnion (fun d => F c d p))).card ≤
        ∑ p ∈ P_large, 15 * (N / (24 * p) + 1) := Finset.sum_le_sum h_inner_p
    have h_sum_rw : ∑ p ∈ P_large, 15 * (N / (24 * p) + 1) =
        15 * (∑ p ∈ P_large, (N / (24 * p)) + P_large.card) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    have h_B_le : B_prime.card ≤ 15 * (∑ p ∈ P_large, (N / (24 * p)) + P_large.card) := by
      rw [← h_sum_rw]
      exact le_trans h_B_bi h_B_sum
    have h_P_card_bound : P_large.card ≤ N / 1800 := by
      have h_LP : L * P_large.card ≤ 14 * N := by
        have := h_s2_1 L Y (7 * N) h2L_le_Y
        dsimp [P_large]
        omega
      have h_25200 : 25200 * P_large.card ≤ L * P_large.card := Nat.mul_le_mul_right P_large.card hL_ge
      have : 25200 * P_large.card ≤ 14 * N := le_trans h_25200 h_LP
      omega
    let P_dyadic : ℕ → Finset ℕ := fun k => (Finset.Icc (2 ^ k * Y + 1) (2 ^ (k + 1) * Y)).filter Nat.Prime
    have h_union_sum : ∀ (A B : Finset ℕ) (g : ℕ → ℕ),
        ∑ x ∈ A ∪ B, g x ≤ ∑ x ∈ A, g x + ∑ x ∈ B, g x := by
      intro A B g
      have h_eq : A ∪ B = A ∪ (B \ A) := (Finset.union_sdiff_self_eq_union).symm
      rw [h_eq, Finset.sum_union Finset.disjoint_sdiff]
      exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset Finset.sdiff_subset) _
    have h_dyadic_ind : ∀ M : ℕ,
        ∑ p ∈ (Finset.range M).biUnion P_dyadic, (N / (24 * p)) ≤ M * (N / (6 * L)) := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        rw [Finset.range_add_one, Finset.biUnion_insert]
        have h1 := h_union_sum (P_dyadic M) ((Finset.range M).biUnion P_dyadic) (fun p => N / (24 * p))
        have h2 := h_s2_3 N Y L M (by omega) h2L_le_Y
        calc ∑ p ∈ P_dyadic M ∪ (Finset.range M).biUnion P_dyadic, (N / (24 * p))
            ≤ ∑ p ∈ P_dyadic M, (N / (24 * p)) + ∑ p ∈ (Finset.range M).biUnion P_dyadic, (N / (24 * p)) := h1
          _ ≤ N / (6 * L) + M * (N / (6 * L)) := Nat.add_le_add h2 ih
          _ = (M + 1) * (N / (6 * L)) := by ring
    have h_P_div_sum : ∑ p ∈ P_large, (N / (24 * p)) ≤ N / 1800 := by
      have h_sub_sum : ∑ p ∈ P_large, (N / (24 * p)) ≤ ∑ p ∈ (Finset.range K).biUnion P_dyadic, (N / (24 * p)) :=
        Finset.sum_le_sum_of_subset hP_sub
      have h_K_bound : ∑ p ∈ P_large, (N / (24 * p)) ≤ K * (N / (6 * L)) :=
        le_trans h_sub_sum (h_dyadic_ind K)
      have h_1800_K : 1800 * K ≤ 6 * L := by
        dsimp [K]
        omega
      have h_mul_le : 1800 * (K * (N / (6 * L))) ≤ N := by
        calc 1800 * (K * (N / (6 * L))) = (1800 * K) * (N / (6 * L)) := by ring
          _ ≤ (6 * L) * (N / (6 * L)) := Nat.mul_le_mul_right _ h_1800_K
          _ ≤ N := Nat.mul_div_le N (6 * L)
      have h_div_K : K * (N / (6 * L)) ≤ N / 1800 := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        linarith
      exact le_trans h_K_bound h_div_K
    omega
  · intro t ht ht3 h_bad
    rcases h_bad with ⟨c, hc, n, hn, p, hp_prime, hYp, hp_dvd_n⟩
    have ht_Icc := Finset.mem_Icc.mp ht
    have hn_Icc := Finset.mem_Icc.mp hn
    have hc_cases : c = 2 ∨ c = 3 ∨ c = 6 := by simpa using hc
    have hn_bounds : 1 ≤ n ∧ n ≤ 7 * N := by
      rcases hc_cases with rfl | rfl | rfl <;> omega
    have hp_le_n : p ≤ n := Nat.le_of_dvd (by omega) hp_dvd_n
    have hp_in_Plarge : p ∈ P_large := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hp_prime⟩
    let d := n - (c * t - 2)
    have hd_in_Sd : d ∈ S_d := by
      rw [Finset.mem_range]
      rcases hc_cases with rfl | rfl | rfl <;> omega
    have h_eq_n : c * t - 2 + d = n := by
      rcases hc_cases with rfl | rfl | rfl <;> omega
    have ht_in_F : t ∈ F c d p := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨ht, ht3⟩, ?_⟩
      rw [h_eq_n]
      exact hp_dvd_n
    rw [Finset.mem_biUnion]
    refine ⟨p, hp_in_Plarge, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨c, hc, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨d, hd_in_Sd, ht_in_F⟩

theorem smooth_pruned_packet_pool_existence (ε : ℚ) (hε : 0 < ε) :
    ∃ N₁ : ℕ, 475600 ≤ N₁ ∧ ∀ N ≥ N₁, ∀ Y : ℕ,
      Y ^ 512 ≤ N ^ 511 → N ^ 511 < (Y + 1) ^ 512 →
      ∀ (l₀ : ℕ) (R₀ : Fin l₀ → ℕ × ℕ),
        l₀ ≤ N / (Nat.ceil (30000 / ε) + 237800) →
        (∀ i : Fin l₀, (R₀ i).2 ≤ (R₀ i).1 + 2) →
        ∃ P : Finset ℕ, P ⊆ Finset.Icc N ((9 * N) / 8) ∧
          (∀ t ∈ P, 3 ∣ t) ∧
          (∀ i : Fin l₀, ∀ t ∈ P,
            ((R₀ i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (R₀ i).1) ∧
            ((R₀ i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (R₀ i).1) ∧
            ((R₀ i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (R₀ i).1)) ∧
          (∀ t ∈ P, ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_pkt t).den = 1) ∧
          N / 4800 ≤ P.card ∧
          (∀ t ∈ P, w_pkt t ≤ 6000 / (1189 * (N : ℚ))) ∧
          3 / 2 - ε ≤ 1189 * ∑ t ∈ P, w_pkt t ∧
          1189 * ∑ t ∈ P, w_pkt t ≤ 3 / 2 + ε :=
by
  have h_w_Icc_natCast : ∀ (D a b : ℕ),
      (∀ n ∈ Finset.Icc a b, 0 < n ∧ n ∣ D) →
      (D : ℚ) * w_Icc a b = ((∑ n ∈ Finset.Icc a b, (D / n) : ℕ) : ℚ) := by
    intro D a b h_dvd
    unfold w_Icc
    rw [Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn_pos, hn_dvd⟩ := h_dvd n hn
    have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_div hn_dvd hn_ne, div_eq_mul_inv]

  have h_s1 : ∀ (N Y t : ℕ), 475600 ≤ N → t ∈ Finset.Icc N ((9 * N) / 8) →
      (4000 / (1189 * (N : ℚ)) ≤ w_pkt t ∧ w_pkt t ≤ 6000 / (1189 * (N : ℚ))) ∧
      ((∀ c ∈ ({2, 3, 6} : Finset ℕ), ∀ n ∈ Finset.Icc (c * t - 2) (c * t + 2),
          ∀ p k : ℕ, Nat.Prime p → p ^ k ∣ n → p ^ k ≤ Y) →
        ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_pkt t).den = 1) := by
    intro N Y t hN ht
    have ht_Icc := Finset.mem_Icc.mp ht
    have h_w_Icc_bounds : ∀ (a b L U : ℕ), 0 < L → L ≤ a → b ≤ U →
        ((b + 1 - a : ℕ) : ℚ) * (U : ℚ)⁻¹ ≤ w_Icc a b ∧
        w_Icc a b ≤ ((b + 1 - a : ℕ) : ℚ) * (L : ℚ)⁻¹ := by
      intro a b L U hL ha hb
      have hL_pos : (0 : ℚ) < (L : ℚ) := Nat.cast_pos.mpr hL
      constructor
      · have h1 : ∀ n ∈ Finset.Icc a b, (U : ℚ)⁻¹ ≤ (n : ℚ)⁻¹ := by
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hn_pos : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr (by omega)
          have hnU : (n : ℚ) ≤ (U : ℚ) := by exact_mod_cast (by omega : n ≤ U)
          exact inv_anti₀ hn_pos hnU
        have h2 := Finset.card_nsmul_le_sum (Finset.Icc a b) (fun n : ℕ => (n : ℚ)⁻¹) (U : ℚ)⁻¹ h1
        simpa [w_Icc, Nat.card_Icc, nsmul_eq_mul] using h2
      · have h1 : ∀ n ∈ Finset.Icc a b, (n : ℚ)⁻¹ ≤ (L : ℚ)⁻¹ := by
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hLn : (L : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : L ≤ n)
          exact inv_anti₀ hL_pos hLn
        have h2 := Finset.sum_le_card_nsmul (Finset.Icc a b) (fun n : ℕ => (n : ℚ)⁻¹) (L : ℚ)⁻¹ h1
        simpa [w_Icc, Nat.card_Icc, nsmul_eq_mul] using h2
    have hb1 := h_w_Icc_bounds (2 * t - 2) (2 * t - 1) (2 * (t - 1)) (2 * (t + 1)) (by omega) (by omega) (by omega)
    have hb2 := h_w_Icc_bounds (2 * t + 1) (2 * t + 2) (2 * (t - 1)) (2 * (t + 1)) (by omega) (by omega) (by omega)
    have hb3 := h_w_Icc_bounds (3 * t - 2) (3 * t + 2) (3 * (t - 1)) (3 * (t + 1)) (by omega) (by omega) (by omega)
    have hb4 := h_w_Icc_bounds (6 * t - 2) (6 * t + 2) (6 * (t - 1)) (6 * (t + 1)) (by omega) (by omega) (by omega)
    have hc1 : 2 * t - 1 + 1 - (2 * t - 2) = 2 := by omega
    have hc2 : 2 * t + 2 + 1 - (2 * t + 1) = 2 := by omega
    have hc3 : 3 * t + 2 + 1 - (3 * t - 2) = 5 := by omega
    have hc4 : 6 * t + 2 + 1 - (6 * t - 2) = 5 := by omega
    rw [hc1] at hb1
    rw [hc2] at hb2
    rw [hc3] at hb3
    rw [hc4] at hb4
    have hcast_sub : ((t - 1 : ℕ) : ℚ) = (t : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    push_cast [hcast_sub] at hb1 hb2 hb3 hb4
    have h_eq_low : 2 * (2 * ((t : ℚ) + 1))⁻¹ + 2 * (2 * ((t : ℚ) + 1))⁻¹ +
        5 * (3 * ((t : ℚ) + 1))⁻¹ + 5 * (6 * ((t : ℚ) + 1))⁻¹ = 9 / (2 * (t : ℚ) + 2) := by
      have h_rew : (2 * (t : ℚ) + 2) = 2 * ((t : ℚ) + 1) := by ring
      rw [h_rew, div_eq_mul_inv]
      repeat rw [mul_inv]
      ring
    have h_eq_high : 2 * (2 * ((t : ℚ) - 1))⁻¹ + 2 * (2 * ((t : ℚ) - 1))⁻¹ +
        5 * (3 * ((t : ℚ) - 1))⁻¹ + 5 * (6 * ((t : ℚ) - 1))⁻¹ = 9 / (2 * (t : ℚ) - 2) := by
      have h_rew : (2 * (t : ℚ) - 2) = 2 * ((t : ℚ) - 1) := by ring
      rw [h_rew, div_eq_mul_inv]
      repeat rw [mul_inv]
      ring
    have hpkt_low : 9 / (2 * (t : ℚ) + 2) ≤ w_pkt t := by
      unfold w_pkt; linarith
    have hpkt_high : w_pkt t ≤ 9 / (2 * (t : ℚ) - 2) := by
      unfold w_pkt; linarith
    have hN_q : (475600 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
    have ht1_q : (N : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht_Icc.1
    have ht2_q : 8 * (t : ℚ) ≤ 9 * (N : ℚ) := by exact_mod_cast (by omega : 8 * t ≤ 9 * N)
    constructor
    · constructor
      · have h_step : 4000 / (1189 * (N : ℚ)) ≤ 9 / (2 * (t : ℚ) + 2) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          linarith
        exact le_trans h_step hpkt_low
      · have h_step : 9 / (2 * (t : ℚ) - 2) ≤ 6000 / (1189 * (N : ℚ)) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          linarith
        exact le_trans hpkt_high h_step
    · intro h_smooth
      set D : ℕ := (Finset.Icc 1 Y).lcm id
      have h_band_dvd : ∀ c ∈ ({2, 3, 6} : Finset ℕ), ∀ n ∈ Finset.Icc (c * t - 2) (c * t + 2),
          0 < n ∧ n ∣ D := by
        intro c hc n hn
        have hn_Icc := Finset.mem_Icc.mp hn
        have hc_cases : c = 2 ∨ c = 3 ∨ c = 6 := by simpa using hc
        have hn_pos : 0 < n := by rcases hc_cases with rfl | rfl | rfl <;> omega
        refine ⟨hn_pos, (Nat.dvd_iff_prime_pow_dvd_dvd D n).mpr ?_⟩
        intro p k hp hpk_n
        have hpk_le : p ^ k ≤ Y := h_smooth c hc n hn p k hp hpk_n
        have hpk_pos : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
        have hpk_mem : p ^ k ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨hpk_pos, hpk_le⟩
        simpa using Finset.dvd_lcm hpk_mem
      have h1 := h_w_Icc_natCast D (2 * t - 2) (2 * t - 1) (fun n hn =>
        h_band_dvd 2 (by simp) n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, by have := (Finset.mem_Icc.mp hn).2; omega⟩))
      have h2 := h_w_Icc_natCast D (2 * t + 1) (2 * t + 2) (fun n hn =>
        h_band_dvd 2 (by simp) n (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega, (Finset.mem_Icc.mp hn).2⟩))
      have h3 := h_w_Icc_natCast D (3 * t - 2) (3 * t + 2) (fun n hn =>
        h_band_dvd 3 (by simp) n hn)
      have h4 := h_w_Icc_natCast D (6 * t - 2) (6 * t + 2) (fun n hn =>
        h_band_dvd 6 (by simp) n hn)
      have h_tot : (D : ℚ) * w_pkt t =
          (((∑ n ∈ Finset.Icc (2 * t - 2) (2 * t - 1), (D / n)) +
            (∑ n ∈ Finset.Icc (2 * t + 1) (2 * t + 2), (D / n)) +
            (∑ n ∈ Finset.Icc (3 * t - 2) (3 * t + 2), (D / n)) +
            (∑ n ∈ Finset.Icc (6 * t - 2) (6 * t + 2), (D / n)) : ℕ) : ℚ) := by
        unfold w_pkt
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, ← h1, ← h2, ← h3, ← h4]
        ring
      rw [h_tot]
      exact Rat.den_natCast _

  have h_s2 : ∀ (l₀ : ℕ) (R₀ : Fin l₀ → ℕ × ℕ),
      (∀ i : Fin l₀, (R₀ i).2 ≤ (R₀ i).1 + 2) →
      ∃ F_conf : Finset ℕ, F_conf.card ≤ 4 * l₀ ∧
        ∀ t : ℕ, 3 ∣ t → t ∉ F_conf → ∀ i : Fin l₀,
          ((R₀ i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (R₀ i).1) ∧
          ((R₀ i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (R₀ i).1) ∧
          ((R₀ i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (R₀ i).1) := by
    intro l₀ R₀ hR₀
    let W : ℕ → Finset ℕ := fun a =>
      {3 * ((a + 2) / 6), 3 * ((a + 2) / 6 + 1), 3 * ((a + 5) / 9), 3 * ((a + 5) / 18)}
    let F_conf : Finset ℕ := Finset.biUnion Finset.univ (fun i : Fin l₀ => W (R₀ i).1)
    refine ⟨F_conf, ?_, ?_⟩
    · have hW_card : ∀ i ∈ (Finset.univ : Finset (Fin l₀)), (W (R₀ i).1).card ≤ 4 := by
        intro i _
        dsimp [W]
        exact le_trans (Finset.card_insert_le _ _)
          (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _)
            (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) (by simp)) 1)) 1)
      have h_bi := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin l₀))) (t := fun i => W (R₀ i).1)
      have h_sum : ∑ i ∈ (Finset.univ : Finset (Fin l₀)), (W (R₀ i).1).card ≤ 4 * l₀ := by
        have h1 := Finset.sum_le_card_nsmul Finset.univ (fun i : Fin l₀ => (W (R₀ i).1).card) 4 hW_card
        simpa [mul_comm] using h1
      exact le_trans h_bi h_sum
    · intro t ht3 ht_not i
      have ht_not_W : t ∉ W (R₀ i).1 := by
        intro h_in
        apply ht_not
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h_in⟩
      dsimp [W] at ht_not_W
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht_not_W
      have h_b := hR₀ i
      omega

  have h_s4 : ∀ (S : Finset ℕ) (f : ℕ → ℚ) (μ δ : ℚ),
      0 ≤ μ → 0 < δ → μ ≤ ∑ t ∈ S, f t →
      (∀ t ∈ S, 0 ≤ f t ∧ f t ≤ δ) →
      ∃ P ⊆ S, μ ≤ ∑ t ∈ P, f t ∧ ∑ t ∈ P, f t ≤ μ + δ ∧
        μ ≤ (P.card : ℚ) * δ := by
    intro S f μ δ hμ hδ h_sum hf
    have h_ind : ∀ (A : Finset ℕ), (∀ t ∈ A, 0 ≤ f t ∧ f t ≤ δ) → μ ≤ ∑ t ∈ A, f t →
        ∃ P ⊆ A, μ ≤ ∑ t ∈ P, f t ∧ ∑ t ∈ P, f t ≤ μ + δ := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro _ h_empty
        simp at h_empty
        have hμ0 : μ = 0 := le_antisymm h_empty hμ
        refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩ <;> simp [hμ0, le_of_lt hδ]
      | @insert a s ha ih =>
        intro h_all h_ins
        by_cases h_s : μ ≤ ∑ t ∈ s, f t
        · obtain ⟨P, hPs, hP1, hP2⟩ := ih (fun t ht => h_all t (Finset.mem_insert_of_mem ht)) h_s
          exact ⟨P, Finset.Subset.trans hPs (Finset.subset_insert a s), hP1, hP2⟩
        · push_neg at h_s
          refine ⟨insert a s, Finset.Subset.refl _, h_ins, ?_⟩
          rw [Finset.sum_insert ha]
          have ha_le : f a ≤ δ := (h_all a (Finset.mem_insert_self a s)).2
          linarith
    obtain ⟨P, hPS, hP1, hP2⟩ := h_ind S hf h_sum
    refine ⟨P, hPS, hP1, hP2, ?_⟩
    have hP_le : ∀ t ∈ P, f t ≤ δ := fun t ht => (hf t (hPS ht)).2
    have h_card := Finset.sum_le_card_nsmul P f δ hP_le
    rw [nsmul_eq_mul] at h_card
    exact le_trans hP1 h_card

  obtain ⟨N_pow, hN_pow, h_pow⟩ := smooth_sieve_pow_bad_bound
  obtain ⟨N_prime, hN_prime, h_prime⟩ := smooth_sieve_prime_bad_bound
  refine ⟨max (max N_pow N_prime) (Nat.ceil (6000 / ε)), ?_, ?_⟩
  · exact le_trans hN_pow (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro N hN Y hY1 hY2 l₀ R₀ hl₀ hR₀
    have hN_pow_le : N_pow ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN_prime_le : N_prime ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN_ceil_le : Nat.ceil (6000 / ε) ≤ N := le_trans (le_max_right _ _) hN
    have hN_475600 : 475600 ≤ N := le_trans hN_pow hN_pow_le
    obtain ⟨B_pow, hB_pow_card, hB_pow_mem⟩ := h_pow N hN_pow_le Y hY1 hY2
    obtain ⟨B_prime, hB_prime_card, hB_prime_mem⟩ := h_prime N hN_prime_le Y hY1 hY2
    let I_N : Finset ℕ := (Finset.Icc N ((9 * N) / 8)).filter (fun t => 3 ∣ t)
    have h_IN_card : N / 24 - 1 ≤ I_N.card := by
      let K := Finset.Icc ((N + 2) / 3) ((9 * N) / 24)
      have h_sub : K.image (fun k => 3 * k) ⊆ I_N := by
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨k, hk, rfl⟩
        rw [Finset.mem_Icc] at hk
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
      have h_inj : Set.InjOn (fun k => 3 * k) K := by
        intro a _ b _ hab
        dsimp at hab
        omega
      have h_card_eq : (K.image (fun k => 3 * k)).card = K.card := Finset.card_image_of_injOn h_inj
      have h_card_le := Finset.card_le_card h_sub
      rw [h_card_eq] at h_card_le
      have hK : K.card = (9 * N) / 24 + 1 - (N + 2) / 3 := by
        simp [K, Nat.card_Icc]
      omega
    let G : Finset ℕ := (I_N \ B_pow) \ B_prime
    have hG_card : N / 45 ≤ G.card := by
      have h1 := Finset.le_card_sdiff B_pow I_N
      have h2 := Finset.le_card_sdiff B_prime (I_N \ B_pow)
      dsimp [G]
      omega
    have hY_pos : 1 ≤ Y := by
      by_contra hY0
      have hY_eq0 : Y = 0 := by omega
      subst hY_eq0
      have h1_le : 1 ≤ N ^ 511 := Nat.one_le_pow 511 N (by omega)
      omega
    have hG_smooth : ∀ t ∈ G, ∀ c ∈ ({2, 3, 6} : Finset ℕ), ∀ n ∈ Finset.Icc (c * t - 2) (c * t + 2),
        ∀ p k : ℕ, Nat.Prime p → p ^ k ∣ n → p ^ k ≤ Y := by
      intro t htG c hc n hn p k hp hpk_n
      have ht_in_diff := Finset.mem_sdiff.mp htG
      have ht_in_IN := (Finset.mem_sdiff.mp ht_in_diff.1).1
      have ht_not_pow := (Finset.mem_sdiff.mp ht_in_diff.1).2
      have ht_not_prime := ht_in_diff.2
      have ht_Icc := (Finset.mem_filter.mp ht_in_IN).1
      have ht_div3 := (Finset.mem_filter.mp ht_in_IN).2
      by_contra h_gt
      push_neg at h_gt
      rcases le_or_gt p Y with hpY | hYp
      · exact ht_not_pow (hB_pow_mem t ht_Icc ht_div3 ⟨c, hc, n, hn, p, k, hp, hpY, hpk_n, h_gt⟩)
      · have hk_pos : 1 ≤ k := by
          by_contra hk0
          have hk_eq0 : k = 0 := by omega
          subst hk_eq0
          simp at h_gt
          omega
        have hp_dvd_pk : p ∣ p ^ k := by
          simpa using Nat.pow_dvd_pow p hk_pos
        have hp_dvd_n : p ∣ n := dvd_trans hp_dvd_pk hpk_n
        exact ht_not_prime (hB_prime_mem t ht_Icc ht_div3 ⟨c, hc, n, hn, p, hp, hYp, hp_dvd_n⟩)
    obtain ⟨F_conf, hF_conf_card, hF_conf_sep⟩ := h_s2 l₀ R₀ hR₀
    let S : Finset ℕ := G \ F_conf
    have hl₀_le : l₀ ≤ N / 237800 := by
      have h_denom : 237800 ≤ Nat.ceil (30000 / ε) + 237800 := by omega
      exact le_trans hl₀ (Nat.div_le_div_left h_denom (by omega))
    have hS_card : N / 48 ≤ S.card := by
      have h1 := Finset.le_card_sdiff F_conf G
      dsimp [S]
      omega
    have hS_sub_G : S ⊆ G := Finset.sdiff_subset
    have hG_sub_IN : G ⊆ I_N := Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset
    have hIN_sub_Icc : I_N ⊆ Finset.Icc N ((9 * N) / 8) := Finset.filter_subset _ _
    have hS_sub_Icc : S ⊆ Finset.Icc N ((9 * N) / 8) :=
      Finset.Subset.trans hS_sub_G (Finset.Subset.trans hG_sub_IN hIN_sub_Icc)
    let f : ℕ → ℚ := fun t => 1189 * w_pkt t
    have hN_pos : (0 : ℚ) < (N : ℚ) := Nat.cast_pos.mpr (by omega)
    have hf_bounds : ∀ t ∈ S, 0 ≤ f t ∧ f t ≤ 6000 / (N : ℚ) := by
      intro t htS
      have ht_s1 := (h_s1 N Y t hN_475600 (hS_sub_Icc htS)).1
      have h_low : 4000 / (N : ℚ) ≤ f t := by
        dsimp [f]
        have := mul_le_mul_of_nonneg_left ht_s1.1 (by norm_num : (0 : ℚ) ≤ 1189)
        ring_nf at this ⊢
        linarith
      have h_high : f t ≤ 6000 / (N : ℚ) := by
        dsimp [f]
        have := mul_le_mul_of_nonneg_left ht_s1.2 (by norm_num : (0 : ℚ) ≤ 1189)
        ring_nf at this ⊢
        linarith
      have h_4000_pos : (0 : ℚ) < 4000 / (N : ℚ) := div_pos (by norm_num) hN_pos
      exact ⟨by linarith, h_high⟩
    have h_sum_S : 3 / 2 ≤ ∑ t ∈ S, f t := by
      have hf_low : ∀ t ∈ S, 4000 / (N : ℚ) ≤ f t := by
        intro t htS
        have ht_s1 := (h_s1 N Y t hN_475600 (hS_sub_Icc htS)).1
        dsimp [f]
        have := mul_le_mul_of_nonneg_left ht_s1.1 (by norm_num : (0 : ℚ) ≤ 1189)
        ring_nf at this ⊢
        linarith
      have h1 := Finset.card_nsmul_le_sum S f (4000 / (N : ℚ)) hf_low
      rw [nsmul_eq_mul] at h1
      have h_nat_ineq : 3 * N ≤ 8000 * S.card := by omega
      have h_q_ineq : 3 * (N : ℚ) ≤ 8000 * (S.card : ℚ) := by exact_mod_cast h_nat_ineq
      have h2 : 3 / 2 ≤ (S.card : ℚ) * (4000 / (N : ℚ)) := by
        have h_eq : (S.card : ℚ) * (4000 / (N : ℚ)) = (4000 * (S.card : ℚ)) / (N : ℚ) := by ring
        rw [h_eq, div_le_div_iff₀ (by norm_num) hN_pos]
        linarith
      exact le_trans h2 h1
    have h_6000_pos : (0 : ℚ) < 6000 / (N : ℚ) := div_pos (by norm_num) hN_pos
    obtain ⟨P, hPS, hP_low, hP_high, hP_card_q⟩ :=
      h_s4 S f (3 / 2) (6000 / (N : ℚ)) (by norm_num) h_6000_pos h_sum_S hf_bounds
    have hP_sub_G : P ⊆ G := Finset.Subset.trans hPS hS_sub_G
    have hP_sub_IN : P ⊆ I_N := Finset.Subset.trans hP_sub_G hG_sub_IN
    have hP_sub_Icc : P ⊆ Finset.Icc N ((9 * N) / 8) := Finset.Subset.trans hP_sub_IN hIN_sub_Icc
    refine ⟨P, hP_sub_Icc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t htP
      exact (Finset.mem_filter.mp (hP_sub_IN htP)).2
    · intro i t htP
      have htS := hPS htP
      have ht_not_conf : t ∉ F_conf := (Finset.mem_sdiff.mp htS).2
      have ht_div3 : 3 ∣ t := (Finset.mem_filter.mp (hP_sub_IN htP)).2
      exact hF_conf_sep t ht_div3 ht_not_conf i
    · intro t htP
      exact (h_s1 N Y t hN_475600 (hP_sub_Icc htP)).2 (hG_smooth t (hP_sub_G htP))
    · have h_mul := mul_le_mul_of_nonneg_right hP_card_q (le_of_lt hN_pos)
      have h_cancel : (P.card : ℚ) * (6000 / (N : ℚ)) * (N : ℚ) = (P.card : ℚ) * 6000 := by
        rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hN_pos)]
      rw [h_cancel] at h_mul
      have h_nat : N ≤ 4000 * P.card := by
        have : (N : ℚ) ≤ 4000 * (P.card : ℚ) := by linarith
        exact_mod_cast this
      omega
    · intro t htP
      exact (h_s1 N Y t hN_475600 (hP_sub_Icc htP)).1.2
    · have h_sum_eq : 1189 * ∑ t ∈ P, w_pkt t = ∑ t ∈ P, f t := by
        dsimp [f]; rw [Finset.mul_sum]
      linarith
    · have h_sum_eq : 1189 * ∑ t ∈ P, w_pkt t = ∑ t ∈ P, f t := by
        dsimp [f]; rw [Finset.mul_sum]
      have h_ceil_q : 6000 / ε ≤ (N : ℚ) := by
        exact le_trans (Nat.le_ceil (6000 / ε)) (by exact_mod_cast hN_ceil_le)
      have h_eps : 6000 / (N : ℚ) ≤ ε := by
        rw [div_le_iff₀ hN_pos]
        have := (div_le_iff₀ hε).mp h_ceil_q
        linarith
      linarith

theorem lcm_jump_prime_power_structure : (∀ q : ℕ, 2 ^ 128 < q →
      ¬ (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189) →
      ∃ p e : ℕ, Nat.Prime p ∧ 1 ≤ e ∧ q = p ^ e ∧
        (Finset.Icc 1 q).lcm id = p * (Finset.Icc 1 (q - 1)).lcm id ∧
        ((Finset.Icc 1 q).lcm id) / 1189 = p * (((Finset.Icc 1 (q - 1)).lcm id) / 1189) ∧
        1189 * (((Finset.Icc 1 (q - 1)).lcm id) / 1189) = (Finset.Icc 1 (q - 1)).lcm id ∧
        1189 * (((Finset.Icc 1 q).lcm id) / 1189) = (Finset.Icc 1 q).lcm id ∧
        Nat.Coprime p (((Finset.Icc 1 q).lcm id) / q)) ∧
    (∀ q₁ q₂ a₁ a₂ : ℕ, 2 ^ 128 < q₁ → q₁ < q₂ →
      ¬ (((Finset.Icc 1 q₂).lcm id) / 1189 ∣ ((Finset.Icc 1 (q₂ - 1)).lcm id) / 1189) →
      1 ≤ a₁ →
      ((((Finset.Icc 1 q₁).lcm id : ℕ) : ℚ) * w_Icc a₁ (a₁ + 1)).den = 1 →
      q₂ ∣ a₂ * (a₂ + 1) →
      a₁ ≠ a₂) :=
by
  have hs1_mono : ∀ m n : ℕ, m ≤ n → (Finset.Icc 1 m).lcm id ∣ (Finset.Icc 1 n).lcm id := by
    intro m n hmn
    apply Finset.lcm_dvd
    intro x hx
    apply Finset.dvd_lcm
    exact Finset.Icc_subset_Icc_right hmn hx

  have hs1_1189 : ∀ n : ℕ, 41 ≤ n → 1189 * (((Finset.Icc 1 n).lcm id) / 1189) = (Finset.Icc 1 n).lcm id := by
    intro n hn
    have h29_mem : 29 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h41_mem : 41 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h29_dvd : 29 ∣ (Finset.Icc 1 n).lcm id := Finset.dvd_lcm h29_mem
    have h41_dvd : 41 ∣ (Finset.Icc 1 n).lcm id := Finset.dvd_lcm h41_mem
    have h_cop : Nat.Coprime 29 41 := by decide
    have h1189_dvd : 1189 ∣ (Finset.Icc 1 n).lcm id := by
      simpa using h_cop.mul_dvd_of_dvd_of_dvd h29_dvd h41_dvd
    exact Nat.mul_div_cancel' h1189_dvd

  have hs1_step : ∀ q : ℕ, 1 ≤ q → q ∣ (Finset.Icc 1 (q - 1)).lcm id →
      ((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189 := by
    intro q hq h_dvd
    have h_le : (Finset.Icc 1 q).lcm id ∣ (Finset.Icc 1 (q - 1)).lcm id := by
      apply Finset.lcm_dvd
      intro x hx
      rw [Finset.mem_Icc] at hx
      rcases eq_or_lt_of_le hx.2 with rfl | hlt
      · exact h_dvd
      · apply Finset.dvd_lcm
        exact Finset.mem_Icc.mpr ⟨hx.1, by omega⟩
    have h_ge : (Finset.Icc 1 (q - 1)).lcm id ∣ (Finset.Icc 1 q).lcm id :=
      hs1_mono (q - 1) q (by omega)
    have h_eq : (Finset.Icc 1 q).lcm id = (Finset.Icc 1 (q - 1)).lcm id :=
      Nat.dvd_antisymm h_le h_ge
    rw [h_eq]

  have hs2 : ∀ q : ℕ, 2 ≤ q → ¬ (q ∣ (Finset.Icc 1 (q - 1)).lcm id) →
      ∃ p e K : ℕ, Nat.Prime p ∧ 1 ≤ e ∧ q = p ^ e ∧
        Nat.Coprime p K ∧
        (Finset.Icc 1 (q - 1)).lcm id = p ^ (e - 1) * K ∧
        (Finset.Icc 1 q).lcm id = p ^ e * K := by
    intro q hq h_not_dvd
    set p := q.minFac
    have hp : Nat.Prime p := Nat.minFac_prime (by omega)
    have hp_dvd : p ∣ q := Nat.minFac_dvd q
    set e := q.factorization p
    have he : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp (by omega) hp_dvd
    set u := q / p ^ e
    have hq_fact : p ^ e * u = q := Nat.ordProj_mul_ordCompl_eq_self q p
    have h_cop_pu : p.Coprime u := Nat.coprime_ordCompl hp (by omega)
    have h_cop_peu : (p ^ e).Coprime u := h_cop_pu.pow_left e
    have hp_ge2 : 2 ≤ p := hp.two_le
    have hpe_ge2 : 2 ≤ p ^ e := by
      calc 2 ≤ p ^ 1 := by simpa using hp_ge2
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
    have hu_pos : 1 ≤ u := by
      rcases eq_or_ne u 0 with hu0 | hu_ne
      · exfalso; rw [hu0, mul_zero] at hq_fact; omega
      · exact Nat.pos_of_ne_zero hu_ne
    have hu_eq1 : u = 1 := by
      by_contra hu_ne1
      have hu_gt1 : 1 < u := lt_of_le_of_ne hu_pos (Ne.symm hu_ne1)
      have hpe_lt_q : p ^ e < q := by
        rw [← hq_fact]
        exact lt_mul_of_one_lt_right (by omega) hu_gt1
      have hu_lt_q : u < q := by
        rw [← hq_fact]
        exact lt_mul_of_one_lt_left hu_pos (by omega)
      have hpe_mem : p ^ e ∈ Finset.Icc 1 (q - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hu_mem : u ∈ Finset.Icc 1 (q - 1) := Finset.mem_Icc.mpr ⟨hu_pos, by omega⟩
      have hpe_dvd : p ^ e ∣ (Finset.Icc 1 (q - 1)).lcm id := Finset.dvd_lcm hpe_mem
      have hu_dvd : u ∣ (Finset.Icc 1 (q - 1)).lcm id := Finset.dvd_lcm hu_mem
      have hq_dvd : p ^ e * u ∣ (Finset.Icc 1 (q - 1)).lcm id :=
        h_cop_peu.mul_dvd_of_dvd_of_dvd hpe_dvd hu_dvd
      rw [hq_fact] at hq_dvd
      exact h_not_dvd hq_dvd
    have hq_eq : q = p ^ e := by
      rw [← hq_fact, hu_eq1, mul_one]
    set M := (Finset.Icc 1 (q - 1)).lcm id
    have hM_ne : M ≠ 0 := by
      rw [ne_eq, Finset.lcm_eq_zero_iff]
      rintro ⟨x, hx, hx0⟩
      rw [Finset.mem_Icc] at hx
      simp only [id_eq] at hx0
      omega
    set k := M.factorization p
    set K := M / p ^ k
    have hM_fact : p ^ k * K = M := Nat.ordProj_mul_ordCompl_eq_self M p
    have h_cop_pK : p.Coprime K := Nat.coprime_ordCompl hp hM_ne
    have hpe1_pos : 1 ≤ p ^ (e - 1) := Nat.one_le_pow (e - 1) p (by omega)
    have hpe1_lt : p ^ (e - 1) < q := by
      rw [hq_eq]
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mpr (by omega)
    have hpe1_mem : p ^ (e - 1) ∈ Finset.Icc 1 (q - 1) := Finset.mem_Icc.mpr ⟨hpe1_pos, by omega⟩
    have hpe1_dvd_M : p ^ (e - 1) ∣ M := Finset.dvd_lcm hpe1_mem
    have hpe1_dvd_pk : p ^ (e - 1) ∣ p ^ k := by
      rw [← hM_fact] at hpe1_dvd_M
      exact (h_cop_pK.pow_left (e - 1)).dvd_of_dvd_mul_right hpe1_dvd_M
    have he1_le_k : e - 1 ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpe1_dvd_pk
    have hk_lt_e : k < e := by
      by_contra h_ge
      have he_le_k : e ≤ k := by omega
      have hpe_dvd_pk : p ^ e ∣ p ^ k := Nat.pow_dvd_pow p he_le_k
      have hq_dvd_M : q ∣ M := by
        rw [hq_eq, ← hM_fact]
        exact dvd_mul_of_dvd_left hpe_dvd_pk K
      exact h_not_dvd hq_dvd_M
    have hk_eq : k = e - 1 := by omega
    have hM_eq : M = p ^ (e - 1) * K := by
      rw [← hM_fact, hk_eq]
    set D_q := (Finset.Icc 1 q).lcm id
    have hpe_eq : p ^ e = p * p ^ (e - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel he, pow_succ']
    have hDq_dvd : D_q ∣ p ^ e * K := by
      apply Finset.lcm_dvd
      intro x hx
      rw [Finset.mem_Icc] at hx
      rcases eq_or_lt_of_le hx.2 with rfl | hlt
      · rw [hq_eq]
        exact dvd_mul_right (p ^ e) K
      · have hx_mem : x ∈ Finset.Icc 1 (q - 1) := Finset.mem_Icc.mpr ⟨hx.1, by omega⟩
        have hx_dvd_M : x ∣ M := Finset.dvd_lcm hx_mem
        have hM_dvd_peK : M ∣ p ^ e * K := by
          rw [hM_eq, hpe_eq, mul_assoc]
          exact dvd_mul_left (p ^ (e - 1) * K) p
        exact dvd_trans hx_dvd_M hM_dvd_peK
    have hpeK_dvd : p ^ e * K ∣ D_q := by
      have hpe_dvd_Dq : p ^ e ∣ D_q := by
        rw [← hq_eq]
        exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, le_refl q⟩)
      have hM_dvd_Dq : M ∣ D_q := hs1_mono (q - 1) q (by omega)
      have hK_dvd_Dq : K ∣ D_q := by
        rw [hM_eq] at hM_dvd_Dq
        exact dvd_of_mul_left_dvd hM_dvd_Dq
      exact (h_cop_pK.pow_left e).mul_dvd_of_dvd_of_dvd hpe_dvd_Dq hK_dvd_Dq
    have hDq_eq : D_q = p ^ e * K := Nat.dvd_antisymm hDq_dvd hpeK_dvd
    exact ⟨p, e, K, hp, he, hq_eq, h_cop_pK, hM_eq, hDq_eq⟩

  have hs3 : ∀ D a : ℕ, 1 ≤ a → ((((D : ℕ) : ℚ) * w_Icc a (a + 1)).den = 1) → a * (a + 1) ∣ D := by
    intro D a ha h_den
    have h_Icc : Finset.Icc a (a + 1) = insert a {a + 1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    have h_not_mem : a ∉ ({a + 1} : Finset ℕ) := by simp
    have hw_eq : w_Icc a (a + 1) = (a : ℚ)⁻¹ + ((a + 1 : ℕ) : ℚ)⁻¹ := by
      unfold w_Icc
      rw [h_Icc, Finset.sum_insert h_not_mem, Finset.sum_singleton]
    set r : ℚ := ((D : ℕ) : ℚ) * w_Icc a (a + 1)
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      rw [hw_eq]
      positivity
    have hnum_nonneg : 0 ≤ r.num := Rat.num_nonneg.mpr hr_nonneg
    set m : ℕ := r.num.toNat
    have hm_int : (m : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
    have hm_rat : ((m : ℕ) : ℚ) = r := by
      have h1 : ((m : ℕ) : ℚ) = (r.num : ℚ) := by exact_mod_cast hm_int
      rw [h1, (Rat.den_eq_one_iff r).mp h_den]
    have ha_ne : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ha1_ne : ((a + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_eq_rat : ((m * (a * (a + 1)) : ℕ) : ℚ) = ((D * (2 * a + 1) : ℕ) : ℚ) := by
      push_cast
      rw [hm_rat]
      dsimp [r]
      rw [hw_eq]
      field_simp [ha_ne, ha1_ne]
      push_cast
      ring
    have h_eq_nat : m * (a * (a + 1)) = D * (2 * a + 1) := by exact_mod_cast h_eq_rat
    have h_dvd_mul : a * (a + 1) ∣ D * (2 * a + 1) := ⟨m, by linarith⟩
    have h_cop1 : a.Coprime (2 * a + 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      apply Nat.dvd_one.mp
      have hd1 : Nat.gcd a (2 * a + 1) ∣ 2 * a := dvd_mul_of_dvd_right (Nat.gcd_dvd_left a (2 * a + 1)) 2
      have hd2 : Nat.gcd a (2 * a + 1) ∣ 2 * a + 1 := Nat.gcd_dvd_right a (2 * a + 1)
      have h_sub := Nat.dvd_sub hd2 hd1
      have h_diff : 2 * a + 1 - 2 * a = 1 := by omega
      rwa [h_diff] at h_sub
    have h_cop2 : (a + 1).Coprime (2 * a + 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      apply Nat.dvd_one.mp
      have hd1 : Nat.gcd (a + 1) (2 * a + 1) ∣ 2 * (a + 1) :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_left (a + 1) (2 * a + 1)) 2
      have hd2 : Nat.gcd (a + 1) (2 * a + 1) ∣ 2 * a + 1 := Nat.gcd_dvd_right (a + 1) (2 * a + 1)
      have h_sub := Nat.dvd_sub hd1 hd2
      have h_diff : 2 * (a + 1) - (2 * a + 1) = 1 := by omega
      rwa [h_diff] at h_sub
    have h_cop_prod : (a * (a + 1)).Coprime (2 * a + 1) := h_cop1.mul_left h_cop2
    exact h_cop_prod.dvd_of_dvd_mul_right h_dvd_mul

  constructor
  · intro q hq h_not_div
    have h_not_dvd : ¬ (q ∣ (Finset.Icc 1 (q - 1)).lcm id) := by
      intro h_dvd
      exact h_not_div (hs1_step q (by omega) h_dvd)
    obtain ⟨p, e, K, hp, he, hq_eq, h_cop_pK, hM_eq, hDq_eq⟩ := hs2 q (by omega) h_not_dvd
    have h1189_prev : 1189 * (((Finset.Icc 1 (q - 1)).lcm id) / 1189) = (Finset.Icc 1 (q - 1)).lcm id :=
      hs1_1189 (q - 1) (by omega)
    have h1189_curr : 1189 * (((Finset.Icc 1 q).lcm id) / 1189) = (Finset.Icc 1 q).lcm id :=
      hs1_1189 q (by omega)
    have hpe_eq : p ^ e = p * p ^ (e - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel he, pow_succ']
    have hD_step : (Finset.Icc 1 q).lcm id = p * (Finset.Icc 1 (q - 1)).lcm id := by
      rw [hDq_eq, hM_eq, hpe_eq, mul_assoc]
    have hL_step : ((Finset.Icc 1 q).lcm id) / 1189 = p * (((Finset.Icc 1 (q - 1)).lcm id) / 1189) := by
      have h_eq : (Finset.Icc 1 q).lcm id = 1189 * (p * (((Finset.Icc 1 (q - 1)).lcm id) / 1189)) := by
        calc (Finset.Icc 1 q).lcm id
            = p * (Finset.Icc 1 (q - 1)).lcm id := hD_step
          _ = p * (1189 * (((Finset.Icc 1 (q - 1)).lcm id) / 1189)) := by rw [h1189_prev]
          _ = 1189 * (p * (((Finset.Icc 1 (q - 1)).lcm id) / 1189)) := by ring
      rw [h_eq, Nat.mul_div_right _ (by decide : 0 < 1189)]
    have hDq_div_q : ((Finset.Icc 1 q).lcm id) / q = K := by
      rw [hDq_eq, ← hq_eq, Nat.mul_div_right K (by omega : 0 < q)]
    refine ⟨p, e, hp, he, hq_eq, hD_step, hL_step, h1189_prev, h1189_curr, ?_⟩
    rwa [hDq_div_q]
  · intro q₁ q₂ a₁ a₂ hq₁ hlt h_not_div₂ ha₁ h_den₁ h_dvd₂ h_eq
    have ha₁_dvd : a₁ * (a₁ + 1) ∣ (Finset.Icc 1 q₁).lcm id :=
      hs3 ((Finset.Icc 1 q₁).lcm id) a₁ ha₁ h_den₁
    rw [h_eq] at ha₁_dvd
    have hq₂_dvd_q₁ : q₂ ∣ (Finset.Icc 1 q₁).lcm id := dvd_trans h_dvd₂ ha₁_dvd
    have hq₁_dvd_q₂ : (Finset.Icc 1 q₁).lcm id ∣ (Finset.Icc 1 (q₂ - 1)).lcm id :=
      hs1_mono q₁ (q₂ - 1) (by omega)
    have hq₂_dvd : q₂ ∣ (Finset.Icc 1 (q₂ - 1)).lcm id := dvd_trans hq₂_dvd_q₁ hq₁_dvd_q₂
    exact h_not_div₂ (hs1_step q₂ (by omega) hq₂_dvd)

theorem dyadic_prime_supply_bound (q : ℕ) (hq : 2 ^ 128 < q) :
    q / (32 * (Nat.log 2 q + 1)) ≤
      ((Finset.Ioc (q / 64) (q / 4)).filter Nat.Prime).card :=
by
  have hs1_lem : ∀ (n m : ℕ), 1 ≤ n →
      (∏ p ∈ n.centralBinom.primeFactors.filter (· ≤ m),
        p ^ (n.centralBinom.factorization p)) ≤
        (2 * n) ^ (2 * n).sqrt * 4 ^ m := by
    intro n m hn
    set B := n.centralBinom
    set S_le := B.primeFactors.filter (· ≤ m)
    set s := (2 * n).sqrt
    set f := fun p : ℕ => p ^ (B.factorization p)
    have h_split := (Finset.prod_filter_mul_prod_filter_not S_le (· ≤ s) f).symm
    rw [h_split]
    set S1 := S_le.filter (· ≤ s)
    set S2 := S_le.filter (fun p => ¬ p ≤ s)
    have h_pow_choose : ∀ p : ℕ, f p ≤ 2 * n := by
      intro p
      dsimp [f, B]
      rw [Nat.centralBinom_eq_two_mul_choose n]
      exact Nat.pow_factorization_choose_le (by omega : 0 < 2 * n)
    have hS1_sub : S1 ⊆ Finset.Icc 1 s := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp.1.1
      rw [Finset.mem_Icc]
      exact ⟨hp_prime.pos, hp.2⟩
    have hS1_card : S1.card ≤ s := by
      have h1 := Finset.card_le_card hS1_sub
      simpa [Nat.card_Icc] using h1
    have h_prod1 : (∏ p ∈ S1, f p) ≤ (2 * n) ^ s := by
      calc (∏ p ∈ S1, f p) ≤ (2 * n) ^ S1.card :=
            Finset.prod_le_pow_card S1 f (2 * n) (fun p _ => h_pow_choose p)
        _ ≤ (2 * n) ^ s := Nat.pow_le_pow_right (by omega) hS1_card
    have h_f_le_p : ∀ p ∈ S2, f p ≤ p := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp.1.1
      have hp_gt : s + 1 ≤ p := by omega
      have h_sqrt_lt : 2 * n < (s + 1) ^ 2 := by
        simpa [sq] using Nat.lt_succ_sqrt (2 * n)
      have h_p2 : (s + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp_gt 2
      have h_fp_lt : f p < p ^ 2 := lt_of_le_of_lt (h_pow_choose p) (lt_of_lt_of_le h_sqrt_lt h_p2)
      have h_exp_lt : B.factorization p < 2 :=
        (Nat.pow_lt_pow_iff_right hp_prime.one_lt).mp h_fp_lt
      have h_exp_le : B.factorization p ≤ 1 := by omega
      calc f p = p ^ (B.factorization p) := rfl
        _ ≤ p ^ 1 := Nat.pow_le_pow_right hp_prime.pos h_exp_le
        _ = p := pow_one p
    have hS2_sub : S2 ⊆ (Finset.range (m + 1)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_of_mem_primeFactors hp.1.1⟩
    have h_prod2 : (∏ p ∈ S2, f p) ≤ 4 ^ m := by
      calc (∏ p ∈ S2, f p) ≤ ∏ p ∈ S2, p := Finset.prod_le_prod' h_f_le_p
        _ ≤ ∏ p ∈ (Finset.range (m + 1)).filter Nat.Prime, p := by
            refine Finset.prod_le_prod_of_subset_of_one_le' hS2_sub ?_
            intro p hp _
            rw [Finset.mem_filter] at hp
            exact hp.2.pos
        _ = primorial m := rfl
        _ ≤ 4 ^ m := primorial_le_4_pow m
    exact Nat.mul_le_mul h_prod1 h_prod2

  have hs2_lem : ∀ (n m : ℕ), 1 ≤ n →
      (∏ p ∈ n.centralBinom.primeFactors.filter (fun p => ¬ p ≤ m),
        p ^ (n.centralBinom.factorization p)) ≤
        (2 * n) ^ ((Finset.Ioc m (2 * n)).filter Nat.Prime).card := by
    intro n m hn
    set B := n.centralBinom
    set S_gt := B.primeFactors.filter (fun p => ¬ p ≤ m)
    set f := fun p : ℕ => p ^ (B.factorization p)
    have h_pow_choose : ∀ p : ℕ, f p ≤ 2 * n := by
      intro p
      dsimp [f, B]
      rw [Nat.centralBinom_eq_two_mul_choose n]
      exact Nat.pow_factorization_choose_le (by omega : 0 < 2 * n)
    have hS_sub : S_gt ⊆ (Finset.Ioc m (2 * n)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp_mem := hp.1
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
      have hp_pos_fac : 0 < B.factorization p := by
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
          rw [Nat.support_factorization]
          exact hp.1))
      have hp_le_2n : p ≤ 2 * n := Nat.le_two_mul_of_factorization_centralBinom_pos hp_pos_fac
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, hp_le_2n⟩, hp_prime⟩
    have h_card : S_gt.card ≤ ((Finset.Ioc m (2 * n)).filter Nat.Prime).card :=
      Finset.card_le_card hS_sub
    calc (∏ p ∈ S_gt, f p) ≤ (2 * n) ^ S_gt.card :=
          Finset.prod_le_pow_card S_gt f (2 * n) (fun p _ => h_pow_choose p)
      _ ≤ (2 * n) ^ ((Finset.Ioc m (2 * n)).filter Nat.Prime).card :=
          Nat.pow_le_pow_right (by omega) h_card

  have hs3_lem : ∀ (C : ℕ),
      4 ^ (q / 8) ≤
        (2 * (q / 8) + 1) * ((2 * (q / 8)) ^ (2 * (q / 8)).sqrt * 4 ^ (q / 64)) *
          (2 * (q / 8)) ^ C →
      q / (32 * (Nat.log 2 q + 1)) ≤ C := by
    intro C h_pow
    set n := q / 8
    set m := q / 64
    set s := (2 * n).sqrt
    set L := Nat.log 2 q
    set K := L + 1
    have hL_ge : 128 ≤ L := by
      have h1 : Nat.log 2 (2 ^ 128) ≤ Nat.log 2 q := Nat.log_mono_right (le_of_lt hq)
      rwa [Nat.log_pow (by decide : 1 < 2)] at h1
    have h2L_le : 2 ^ L ≤ q := Nat.pow_log_le_self 2 (by omega)
    have hq_lt_2K : q < 2 ^ K := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q
    have h2n1_le : 2 * n + 1 ≤ 2 ^ K := by omega
    have h2n_le : 2 * n ≤ 2 ^ K := by omega
    have h4n_eq : 2 ^ (2 * n) = 4 ^ n := by
      rw [pow_mul]
      norm_num
    have h4m_eq : 4 ^ m = 2 ^ (2 * m) := by
      rw [pow_mul]
      norm_num
    have h2ns_le : (2 * n) ^ s ≤ 2 ^ (K * s) := by
      calc (2 * n) ^ s ≤ (2 ^ K) ^ s := Nat.pow_le_pow_left h2n_le s
        _ = 2 ^ (K * s) := (pow_mul 2 K s).symm
    have h2nC_le : (2 * n) ^ C ≤ 2 ^ (K * C) := by
      calc (2 * n) ^ C ≤ (2 ^ K) ^ C := Nat.pow_le_pow_left h2n_le C
        _ = 2 ^ (K * C) := (pow_mul 2 K C).symm
    have h_rhs_le : (2 * n + 1) * ((2 * n) ^ s * 4 ^ m) * (2 * n) ^ C ≤
        2 ^ (K + (K * s + 2 * m) + K * C) := by
      calc (2 * n + 1) * ((2 * n) ^ s * 4 ^ m) * (2 * n) ^ C
          ≤ 2 ^ K * (2 ^ (K * s) * 2 ^ (2 * m)) * 2 ^ (K * C) := by
            apply Nat.mul_le_mul _ h2nC_le
            apply Nat.mul_le_mul h2n1_le
            rw [h4m_eq]
            exact Nat.mul_le_mul_right (2 ^ (2 * m)) h2ns_le
        _ = 2 ^ (K + (K * s + 2 * m) + K * C) := by
            rw [← pow_add, ← pow_add, ← pow_add]
    have h_pow2_le : 2 ^ (2 * n) ≤ 2 ^ (K + (K * s + 2 * m) + K * C) := by
      rw [h4n_eq]
      exact le_trans h_pow h_rhs_le
    have h_exp_le : 2 * n ≤ K + (K * s + 2 * m) + K * C :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h_pow2_le
    have h2n_lt_2Lm1 : 2 * n < 2 ^ (L - 1) := by
      have h_eq : 2 ^ K = 4 * 2 ^ (L - 1) := by
        have hK_eq : K = 2 + (L - 1) := by omega
        rw [hK_eq, pow_add]
        norm_num
      omega
    have h_Lm1_le : L - 1 ≤ 2 * (L / 2) := by omega
    have h2Lm1_le : 2 ^ (L - 1) ≤ (2 ^ (L / 2)) ^ 2 := by
      calc 2 ^ (L - 1) ≤ 2 ^ (2 * (L / 2)) := Nat.pow_le_pow_right (by decide) h_Lm1_le
        _ = (2 ^ (L / 2)) ^ 2 := by rw [← pow_mul, mul_comm]
    have hs_sq_lt : s ^ 2 < (2 ^ (L / 2)) ^ 2 := by
      have hs_sq : s ^ 2 ≤ 2 * n := by
        simpa [sq] using Nat.sqrt_le (2 * n)
      exact lt_of_le_of_lt hs_sq (lt_of_lt_of_le h2n_lt_2Lm1 h2Lm1_le)
    have hs_lt : s < 2 ^ (L / 2) := (Nat.pow_lt_pow_iff_left (by decide)).mp hs_sq_lt
    have hs1_le : 1 + s ≤ 2 ^ (L / 2) := by omega
    have h_L4 : L / 4 < 2 ^ (L / 4) := Nat.lt_two_pow_self
    have hK_le_pow : K ≤ 2 ^ (2 + L / 4) := by
      have h1 : K ≤ 4 * (L / 4 + 1) := by omega
      have h2 : 4 * (L / 4 + 1) ≤ 4 * 2 ^ (L / 4) := Nat.mul_le_mul_left 4 (by omega)
      have h3 : 4 * 2 ^ (L / 4) = 2 ^ (2 + L / 4) := by
        rw [pow_add]
        norm_num
      omega
    have hKs_le : K * (1 + s) ≤ 2 ^ (L - 4) := by
      have h_exp : 2 + L / 4 + L / 2 ≤ L - 4 := by omega
      calc K * (1 + s) ≤ 2 ^ (2 + L / 4) * 2 ^ (L / 2) := Nat.mul_le_mul hK_le_pow hs1_le
        _ = 2 ^ (2 + L / 4 + L / 2) := (pow_add 2 (2 + L / 4) (L / 2)).symm
        _ ≤ 2 ^ (L - 4) := Nat.pow_le_pow_right (by decide) h_exp
    have h16_pow : 16 * 2 ^ (L - 4) ≤ q := by
      have h_eq : 16 * 2 ^ (L - 4) = 2 ^ L := by
        have hL_eq : L = 4 + (L - 4) := by omega
        nth_rw 2 [hL_eq]
        rw [pow_add]
        norm_num
      omega
    have hKs_q16 : K * (1 + s) ≤ q / 16 := by omega
    have h_Ks_expand : K + K * s = K * (1 + s) := by ring
    have h_KC : q ≤ 32 * (K * C) := by omega
    have h_C_mul : (32 * K) * (q / (32 * K)) ≤ (32 * K) * C := by
      have h_div : (32 * K) * (q / (32 * K)) ≤ q := Nat.mul_div_le q (32 * K)
      linarith
    exact Nat.le_of_mul_le_mul_left h_C_mul (by omega)

  set n := q / 8
  set m := q / 64
  have hn : 1 ≤ n := by omega
  set B := n.centralBinom
  have hB_pos : 0 < B := Nat.centralBinom_pos n
  have h4n_le : 4 ^ n ≤ (2 * n + 1) * B := by
    have h := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
    rwa [← Nat.centralBinom_eq_two_mul_choose n] at h
  have hB_fac : B = ∏ p ∈ B.primeFactors, p ^ (B.factorization p) :=
    (Nat.factorization_prod_pow_eq_self (ne_of_gt hB_pos)).symm
  have hB_split : (∏ p ∈ B.primeFactors, p ^ (B.factorization p)) =
      (∏ p ∈ B.primeFactors.filter (· ≤ m), p ^ (B.factorization p)) *
      (∏ p ∈ B.primeFactors.filter (fun p => ¬ p ≤ m), p ^ (B.factorization p)) :=
    (Finset.prod_filter_mul_prod_filter_not B.primeFactors (· ≤ m) (fun p => p ^ (B.factorization p))).symm
  have hs1 := hs1_lem n m hn
  have hs2 := hs2_lem n m hn
  set C0 := ((Finset.Ioc m (2 * n)).filter Nat.Prime).card
  set C := ((Finset.Ioc m (q / 4)).filter Nat.Prime).card
  have hC0_le_C : C0 ≤ C := by
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    exact Finset.Ioc_subset_Ioc_right (by omega : 2 * n ≤ q / 4)
  have h_pow_C : (2 * n) ^ C0 ≤ (2 * n) ^ C := Nat.pow_le_pow_right (by omega) hC0_le_C
  have h_B_le : B ≤ ((2 * n) ^ (2 * n).sqrt * 4 ^ m) * (2 * n) ^ C := by
    rw [hB_fac, hB_split]
    exact Nat.mul_le_mul hs1 (le_trans hs2 h_pow_C)
  have h_pow : 4 ^ n ≤ (2 * n + 1) * ((2 * n) ^ (2 * n).sqrt * 4 ^ m) * (2 * n) ^ C := by
    calc 4 ^ n ≤ (2 * n + 1) * B := h4n_le
      _ ≤ (2 * n + 1) * (((2 * n) ^ (2 * n).sqrt * 4 ^ m) * (2 * n) ^ C) :=
          Nat.mul_le_mul_left (2 * n + 1) h_B_le
      _ = (2 * n + 1) * ((2 * n) ^ (2 * n).sqrt * 4 ^ m) * (2 * n) ^ C := by ring
  exact hs3_lem C h_pow

theorem prime_cofactor_selection_and_bad_prime_bound (q p e : ℕ)
    (hq : 2 ^ 128 < q) (hp : Nat.Prime p) (he : 1 ≤ e) (hq_eq : q = p ^ e) :
    ∃ (G_q : Finset ℕ) (c_of d_of a_of : ℕ → ℕ),
      G_q ⊆ (Finset.Ioc (q / 64) (q / 4)).filter Nat.Prime ∧
      ((Finset.Ioc (q / 64) (q / 4)).filter Nat.Prime).card ≤ G_q.card + 512 ∧
      (∀ l ∈ G_q,
        1 ≤ c_of l ∧
        c_of l < l ∧
        Nat.Coprime (c_of l) p ∧
        1 ≤ d_of l ∧
        d_of l < q ∧
        Nat.Coprime l (d_of l) ∧
        ((a_of l = q * c_of l ∧ a_of l + 1 = l * d_of l) ∨
         (a_of l + 1 = q * c_of l ∧ a_of l = l * d_of l))) :=
by
  classical
  obtain ⟨P_q, hP_def⟩ : ∃ P_q : Finset ℕ, P_q = (Finset.Ioc (q / 64) (q / 4)).filter Nat.Prime := ⟨_, rfl⟩

  
  have h_s1 : ∀ l : ℕ, l ∈ P_q →
      ∃ c d a : ℕ,
        1 ≤ c ∧ c < l ∧ Nat.Coprime c p ∧
        1 ≤ d ∧ d < q ∧
        ((a = q * c ∧ a + 1 = l * d) ∨ (a + 1 = q * c ∧ a = l * d)) := by
    intro l hl_mem
    rw [hP_def] at hl_mem
    have hl_filter := Finset.mem_filter.mp hl_mem
    have hl_Ioc := Finset.mem_Ioc.mp hl_filter.1
    have hl_gt : q / 64 < l := hl_Ioc.1
    have hl_le : l ≤ q / 4 := hl_Ioc.2
    have hl_prime : Nat.Prime l := hl_filter.2
    have h_ne : p ≠ l := by
      intro h_eq
      rcases eq_or_lt_of_le he with rfl | he2
      · rw [pow_one, h_eq] at hq_eq
        omega
      · have h_e_split : e = 2 + (e - 2) := by omega
        have h_pow_ge : p ^ 2 ≤ q := by
          rw [hq_eq, h_e_split, Nat.pow_add]
          exact Nat.le_mul_of_pos_right (p ^ 2) (Nat.pow_pos hp.pos)
        rw [h_eq] at h_pow_ge
        have h1 : q < 64 * l := by omega
        have h2 : 64 < l := by omega
        nlinarith
    have h_cop_pl : Nat.Coprime p l := (Nat.coprime_primes hp hl_prime).mpr h_ne
    have h_cop_ql : Nat.Coprime q l := by
      rw [hq_eq]
      exact h_cop_pl.pow_left e
    haveI : Fact l.Prime := ⟨hl_prime⟩
    have hq_zmod_ne : (q : ZMod l) ≠ 0 := by
      intro h_zero
      have h_mod : q % l = 0 := by
        have h1 : (q : ZMod l).val = q % l := ZMod.val_natCast l q
        rw [h_zero, ZMod.val_zero] at h1
        exact h1.symm
      have h_dvd : l ∣ q := Nat.dvd_of_mod_eq_zero h_mod
      have h_one : l ∣ 1 := by
        rw [← h_cop_ql.gcd_eq_one]
        exact Nat.dvd_gcd h_dvd (dvd_refl l)
      exact hl_prime.not_dvd_one h_one
    set c_minus : ℕ := ((q : ZMod l)⁻¹).val
    have hc_minus_lt : c_minus < l := ZMod.val_lt _
    have hc_minus_zmod : (c_minus : ZMod l) = (q : ZMod l)⁻¹ := ZMod.natCast_zmod_val _
    have hqc_zmod : ((q * c_minus : ℕ) : ZMod l) = 1 := by
      rw [Nat.cast_mul, hc_minus_zmod, mul_inv_cancel₀ hq_zmod_ne]
    have hqc_mod : (q * c_minus) % l = 1 := by
      have h1 : ((q * c_minus : ℕ) : ZMod l).val = (q * c_minus) % l := ZMod.val_natCast l (q * c_minus)
      rw [hqc_zmod, ZMod.val_one] at h1
      exact h1.symm
    have hc_minus_pos : 1 ≤ c_minus := by
      rcases eq_or_ne c_minus 0 with h0 | hpos
      · exfalso
        rw [h0, mul_zero, Nat.zero_mod] at hqc_mod
        omega
      · omega
    set d_minus : ℕ := (q * c_minus) / l
    have hqc_minus_eq : q * c_minus = l * d_minus + 1 := by
      have h_div_mod := Nat.div_add_mod (q * c_minus) l
      dsimp [d_minus]
      omega
    have hd_minus_pos : 1 ≤ d_minus := by nlinarith
    have hd_minus_lt : d_minus < q := by nlinarith
    set c_plus : ℕ := l - c_minus
    set d_plus : ℕ := q - d_minus
    have hc_plus_pos : 1 ≤ c_plus := by omega
    have hc_plus_lt : c_plus < l := by omega
    have hd_plus_pos : 1 ≤ d_plus := by omega
    have hd_plus_lt : d_plus < q := by omega
    have hd_plus_eq : q * c_plus + 1 = l * d_plus := by
      have h_c_sum : c_plus + c_minus = l := by omega
      have h_d_sum : d_plus + d_minus = q := by omega
      nlinarith
    by_cases h_cop_plus : Nat.Coprime c_plus p
    · refine ⟨c_plus, d_plus, q * c_plus, hc_plus_pos, hc_plus_lt, h_cop_plus,
        hd_plus_pos, hd_plus_lt, Or.inl ⟨rfl, hd_plus_eq⟩⟩
    · have h_cop_minus : Nat.Coprime c_minus p := by
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro hp_dvd_minus
        have hp_dvd_plus : p ∣ c_plus := by
          rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, not_not] at h_cop_plus
          exact h_cop_plus
        have hp_dvd_l : p ∣ l := by
          have h_add : c_plus + c_minus = l := by omega
          rw [← h_add]
          exact dvd_add hp_dvd_plus hp_dvd_minus
        exact (hp.coprime_iff_not_dvd.mp h_cop_pl) hp_dvd_l
      refine ⟨c_minus, d_minus, q * c_minus - 1, hc_minus_pos, hc_minus_lt, h_cop_minus,
        hd_minus_pos, hd_minus_lt, Or.inr ⟨by omega, by omega⟩⟩

  
  have h_s2_lt : ∀ (k l₁ l₂ : ℕ),
      l₂ < l₁ → l₁ ≤ q / 4 → 1 ≤ l₂ →
      Nat.Coprime q k → Nat.Coprime q l₁ →
      q ∣ k * (l₁ ^ 2 - l₂ ^ 2) → False := by
    intro k l₁ l₂ h_lt hl₁_le hl₂_pos h_cop_qk h_cop_ql₁ h_dvd_mul
    have h_dvd_diff : q ∣ l₁ ^ 2 - l₂ ^ 2 := h_cop_qk.dvd_of_dvd_mul_left h_dvd_mul
    rw [Nat.sq_sub_sq] at h_dvd_diff
    obtain ⟨k₁, k₂, hk₁_dvd, hk₂_dvd, hk_prod⟩ := Nat.dvd_mul.mp h_dvd_diff
    have hk₁_le : k₁ ≤ l₁ + l₂ := Nat.le_of_dvd (by omega) hk₁_dvd
    have hk₂_le : k₂ ≤ l₁ - l₂ := Nat.le_of_dvd (by omega) hk₂_dvd
    have h2k₁ : 2 * k₁ < q := by omega
    have h4k₂ : 4 * k₂ < q := by omega
    have hk₁_gt2 : 2 < k₁ := by nlinarith
    have hk₂_gt2 : 2 < k₂ := by nlinarith
    have hk₁_dvd_q : k₁ ∣ q := ⟨k₂, hk_prod.symm⟩
    have hk₂_dvd_q : k₂ ∣ q := ⟨k₁, by linarith [hk_prod]⟩
    have hk₁_dvd_pe : k₁ ∣ p ^ e := hq_eq ▸ hk₁_dvd_q
    have hk₂_dvd_pe : k₂ ∣ p ^ e := hq_eq ▸ hk₂_dvd_q
    obtain ⟨i₁, _, hk₁_eq⟩ := (Nat.dvd_prime_pow hp).mp hk₁_dvd_pe
    obtain ⟨i₂, _, hk₂_eq⟩ := (Nat.dvd_prime_pow hp).mp hk₂_dvd_pe
    have h_sum_diff : (l₁ + l₂) + (l₁ - l₂) = 2 * l₁ := by omega
    rcases le_total i₁ i₂ with hi | hi
    · have hk₁_dvd_k₂ : k₁ ∣ k₂ := by
        rw [hk₁_eq, hk₂_eq]
        exact Nat.pow_dvd_pow p hi
      have hk₁_dvd_2l₁ : k₁ ∣ 2 * l₁ := by
        rw [← h_sum_diff]
        exact dvd_add hk₁_dvd (dvd_trans hk₁_dvd_k₂ hk₂_dvd)
      have h_cop_k₁ : Nat.Coprime k₁ l₁ := h_cop_ql₁.coprime_dvd_left hk₁_dvd_q
      have hk₁_dvd_2 : k₁ ∣ 2 := h_cop_k₁.dvd_of_dvd_mul_right hk₁_dvd_2l₁
      have hk₁_le_2 : k₁ ≤ 2 := Nat.le_of_dvd (by omega) hk₁_dvd_2
      omega
    · have hk₂_dvd_k₁ : k₂ ∣ k₁ := by
        rw [hk₁_eq, hk₂_eq]
        exact Nat.pow_dvd_pow p hi
      have hk₂_dvd_2l₁ : k₂ ∣ 2 * l₁ := by
        rw [← h_sum_diff]
        exact dvd_add (dvd_trans hk₂_dvd_k₁ hk₁_dvd) hk₂_dvd
      have h_cop_k₂ : Nat.Coprime k₂ l₁ := h_cop_ql₁.coprime_dvd_left hk₂_dvd_q
      have hk₂_dvd_2 : k₂ ∣ 2 := h_cop_k₂.dvd_of_dvd_mul_right hk₂_dvd_2l₁
      have hk₂_le_2 : k₂ ≤ 2 := Nat.le_of_dvd (by omega) hk₂_dvd_2
      omega

  have h_s2_cop : ∀ (k l c : ℕ),
      (q * c + 1 = k * l ^ 2 ∨ q * c = k * l ^ 2 + 1) →
      Nat.Coprime q k ∧ Nat.Coprime q l := by
    intro k l c h_eq
    have h_cop_prod : Nat.Coprime q (k * l ^ 2) := by
      rw [Nat.Coprime, Nat.gcd_eq_one_iff]
      intro g hg_q hg_kl
      have hg_qc : g ∣ q * c := dvd_mul_of_dvd_left hg_q c
      have hg_one : g ∣ 1 := by
        rcases h_eq with h1 | h1
        · have h_sub : k * l ^ 2 - q * c = 1 := by omega
          rw [← h_sub]
          exact Nat.dvd_sub hg_kl hg_qc
        · have h_sub : q * c - k * l ^ 2 = 1 := by omega
          rw [← h_sub]
          exact Nat.dvd_sub hg_qc hg_kl
      exact Nat.dvd_one.mp hg_one
    have h_cop_k : Nat.Coprime q k := h_cop_prod.coprime_mul_right_right
    have h_cop_l2 : Nat.Coprime q (l ^ 2) := h_cop_prod.coprime_mul_left_right
    have h_cop_l : Nat.Coprime q l := by
      rw [sq] at h_cop_l2
      exact h_cop_l2.coprime_mul_right_right
    exact ⟨h_cop_k, h_cop_l⟩

  have h_s2 : ∀ (k l₁ l₂ c₁ c₂ : ℕ),
      1 ≤ l₁ → l₁ ≤ q / 4 →
      1 ≤ l₂ → l₂ ≤ q / 4 →
      ((q * c₁ + 1 = k * l₁ ^ 2 ∧ q * c₂ + 1 = k * l₂ ^ 2) ∨
       (q * c₁ = k * l₁ ^ 2 + 1 ∧ q * c₂ = k * l₂ ^ 2 + 1)) →
      l₁ = l₂ := by
    intro k l₁ l₂ c₁ c₂ hl₁_pos hl₁_le hl₂_pos hl₂_le h_rel
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · obtain ⟨h_cop_k, h_cop_l₂⟩ := h_s2_cop k l₂ c₂
        (h_rel.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
      have h_dvd : q ∣ k * (l₂ ^ 2 - l₁ ^ 2) := by
        refine ⟨c₂ - c₁, ?_⟩
        rw [Nat.mul_sub, Nat.mul_sub]
        rcases h_rel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      exact h_s2_lt k l₂ l₁ h_lt hl₂_le hl₁_pos h_cop_k h_cop_l₂ h_dvd
    · obtain ⟨h_cop_k, h_cop_l₁⟩ := h_s2_cop k l₁ c₁
        (h_rel.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
      have h_dvd : q ∣ k * (l₁ ^ 2 - l₂ ^ 2) := by
        refine ⟨c₁ - c₂, ?_⟩
        rw [Nat.mul_sub, Nat.mul_sub]
        rcases h_rel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      exact h_s2_lt k l₁ l₂ h_gt hl₁_le hl₂_pos h_cop_k h_cop_l₁ h_dvd

  
  have h_ex_of : ∃ (c_of d_of a_of : ℕ → ℕ), ∀ l ∈ P_q,
      1 ≤ c_of l ∧ c_of l < l ∧ Nat.Coprime (c_of l) p ∧
      1 ≤ d_of l ∧ d_of l < q ∧
      ((a_of l = q * c_of l ∧ a_of l + 1 = l * d_of l) ∨
       (a_of l + 1 = q * c_of l ∧ a_of l = l * d_of l)) := by
    let c_fn : ℕ → ℕ := fun l =>
      if hl : l ∈ P_q then Classical.choose (h_s1 l hl) else 0
    let d_fn : ℕ → ℕ := fun l =>
      if hl : l ∈ P_q then Classical.choose (Classical.choose_spec (h_s1 l hl)) else 0
    let a_fn : ℕ → ℕ := fun l =>
      if hl : l ∈ P_q then Classical.choose (Classical.choose_spec (Classical.choose_spec (h_s1 l hl))) else 0
    refine ⟨c_fn, d_fn, a_fn, fun l hl => ?_⟩
    have hc_eq : c_fn l = Classical.choose (h_s1 l hl) := dif_pos hl
    have hd_eq : d_fn l = Classical.choose (Classical.choose_spec (h_s1 l hl)) := dif_pos hl
    have ha_eq : a_fn l = Classical.choose (Classical.choose_spec (Classical.choose_spec (h_s1 l hl))) := dif_pos hl
    rw [hc_eq, hd_eq, ha_eq]
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h_s1 l hl)))

  obtain ⟨c_of, d_of, a_of, h_of_spec⟩ := h_ex_of
  obtain ⟨G_q, hG_def⟩ : ∃ G_q : Finset ℕ, G_q = P_q.filter (fun l => Nat.Coprime l (d_of l)) := ⟨_, rfl⟩
  obtain ⟨B_q, hB_def⟩ : ∃ B_q : Finset ℕ, B_q = P_q.filter (fun l => ¬ Nat.Coprime l (d_of l)) := ⟨_, rfl⟩
  obtain ⟨f, hf_def⟩ : ∃ f : ℕ → ℕ × ℕ, f = fun l => (d_of l / l, if a_of l = q * c_of l then 0 else 1) := ⟨_, rfl⟩
  obtain ⟨T_box, hT_def⟩ : ∃ T_box : Finset (ℕ × ℕ), T_box = Finset.Icc 1 63 ×ˢ Finset.range 2 := ⟨_, rfl⟩

  have h_part : G_q.card + B_q.card = P_q.card := by
    rw [hG_def, hB_def]
    exact Finset.card_filter_add_card_filter_not (s := P_q) (p := fun l => Nat.Coprime l (d_of l))

  have h_bad_div : ∀ l ∈ B_q,
      1 ≤ l ∧ l ≤ q / 4 ∧ 1 ≤ d_of l / l ∧ d_of l / l ≤ 63 ∧
      ((a_of l = q * c_of l ∧ q * c_of l + 1 = (d_of l / l) * l ^ 2) ∨
       (a_of l ≠ q * c_of l ∧ q * c_of l = (d_of l / l) * l ^ 2 + 1)) := by
    intro l hl_B
    rw [hB_def] at hl_B
    have hl_P : l ∈ P_q := (Finset.mem_filter.mp hl_B).1
    have hl_not_cop : ¬ Nat.Coprime l (d_of l) := (Finset.mem_filter.mp hl_B).2
    have hl_P' := hl_P
    rw [hP_def] at hl_P'
    have hl_filter := Finset.mem_filter.mp hl_P'
    have hl_Ioc := Finset.mem_Ioc.mp hl_filter.1
    have hl_gt : q / 64 < l := hl_Ioc.1
    have hl_le : l ≤ q / 4 := hl_Ioc.2
    have hl_prime : Nat.Prime l := hl_filter.2
    obtain ⟨hc_pos, _, _, hd_pos, hd_lt, ha_rel⟩ := h_of_spec l hl_P
    have hl_dvd_d : l ∣ d_of l := by
      rw [hl_prime.coprime_iff_not_dvd, not_not] at hl_not_cop
      exact hl_not_cop
    have hd_eq : l * (d_of l / l) = d_of l := Nat.mul_div_cancel' hl_dvd_d
    have hk_pos : 1 ≤ d_of l / l := by nlinarith
    have hk_le : d_of l / l ≤ 63 := by
      have h1 : q < 64 * l := by omega
      nlinarith
    have hld_eq : l * d_of l = (d_of l / l) * l ^ 2 := by nlinarith
    refine ⟨by omega, hl_le, hk_pos, hk_le, ?_⟩
    rcases ha_rel with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨h1, by omega⟩
    · right
      exact ⟨by omega, by omega⟩

  have hf_maps : ∀ l ∈ B_q, f l ∈ T_box := by
    intro l hl_B
    obtain ⟨_, _, hk_pos, hk_le, _⟩ := h_bad_div l hl_B
    rw [hT_def, hf_def, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    dsimp only
    refine ⟨⟨hk_pos, hk_le⟩, ?_⟩
    split_ifs <;> omega

  have hf_inj : Set.InjOn f B_q := by
    intro l₁ hl₁ l₂ hl₂ h_feq
    obtain ⟨hl₁_pos, hl₁_le, _, _, h_rel₁⟩ := h_bad_div l₁ hl₁
    obtain ⟨hl₂_pos, hl₂_le, _, _, h_rel₂⟩ := h_bad_div l₂ hl₂
    rw [hf_def] at h_feq
    have h_fst : d_of l₁ / l₁ = d_of l₂ / l₂ := congr_arg Prod.fst h_feq
    have h_snd : (if a_of l₁ = q * c_of l₁ then 0 else 1) =
        (if a_of l₂ = q * c_of l₂ then 0 else 1) := congr_arg Prod.snd h_feq
    set k := d_of l₁ / l₁
    rw [← h_fst] at h_rel₂
    rcases h_rel₁ with ⟨h1_eq, h1_sq⟩ | ⟨h1_ne, h1_sq⟩
    · rcases h_rel₂ with ⟨h2_eq, h2_sq⟩ | ⟨h2_ne, h2_sq⟩
      · exact h_s2 k l₁ l₂ (c_of l₁) (c_of l₂) hl₁_pos hl₁_le hl₂_pos hl₂_le (Or.inl ⟨h1_sq, h2_sq⟩)
      · rw [if_pos h1_eq, if_neg h2_ne] at h_snd
        omega
    · rcases h_rel₂ with ⟨h2_eq, h2_sq⟩ | ⟨h2_ne, h2_sq⟩
      · rw [if_neg h1_ne, if_pos h2_eq] at h_snd
        omega
      · exact h_s2 k l₁ l₂ (c_of l₁) (c_of l₂) hl₁_pos hl₁_le hl₂_pos hl₂_le (Or.inr ⟨h1_sq, h2_sq⟩)

  have hB_card : B_q.card ≤ T_box.card :=
    Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hT_card : T_box.card = 126 := by
    rw [hT_def, Finset.card_product, Nat.card_Icc, Finset.card_range]

  refine ⟨G_q, c_of, d_of, a_of, ?_, by rw [← hP_def]; omega, ?_⟩
  · rw [hG_def, ← hP_def]
    exact Finset.filter_subset _ _
  · intro l hl_G
    rw [hG_def] at hl_G
    have hl_P : l ∈ P_q := (Finset.mem_filter.mp hl_G).1
    have hl_cop : Nat.Coprime l (d_of l) := (Finset.mem_filter.mp hl_G).2
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_of_spec l hl_P
    exact ⟨h1, h2, h3, h4, h5, hl_cop, h6⟩

theorem single_prime_power_cofactor_reservoir_construction (q p e : ℕ)
    (hq : 2 ^ 128 < q) (hp : Nat.Prime p) (he : 1 ≤ e) (hq_eq : q = p ^ e) :
    ∃ (I : ℕ → ℕ × ℕ) (c : ℕ → ℕ),
      (∀ j < q / (512 * (Nat.log 2 q + 1)),
        q / (1024 * (Nat.log 2 q + 1)) ≤ c j ∧
        c j < q / 4 ∧
        Nat.Coprime (c j) p ∧
        q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ (I j).1 ∧
        (I j).2 = (I j).1 + 1 ∧
        (I j).2 ≤ q ^ 2 / 2 ∧
        w_Icc (I j).1 (I j).2 ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2 ∧
        q ∣ (I j).1 * ((I j).1 + 1) ∧
        ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).den = 1 ∧
        ((p : ℤ) ∣ ((c j : ℤ) * ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).num -
          (((Finset.Icc 1 q).lcm id / q : ℕ) : ℤ)))) ∧
      (∀ j₁ < q / (512 * (Nat.log 2 q + 1)), ∀ j₂ < q / (512 * (Nat.log 2 q + 1)), j₁ ≠ j₂ →
        c j₁ ≠ c j₂ ∧
        ((I j₁).2 + 1 < (I j₂).1 ∨ (I j₂).2 + 1 < (I j₁).1)) :=
by
  classical
  have h_supply := dyadic_prime_supply_bound q hq
  obtain ⟨G_q, c_of, d_of, a_of, hG_sub, hG_bad, hG_props⟩ :=
    prime_cofactor_selection_and_bad_prime_bound q p e hq hp he hq_eq
  have hG_card : q / (32 * (Nat.log 2 q + 1)) ≤ G_q.card + 512 := le_trans h_supply hG_bad

  
  have h_div_card : ∀ N : ℕ, 1 ≤ N → N ≤ q ^ 2 / 4 →
      (G_q.filter (fun l => l ∣ N)).card ≤ 2 := by
    intro N hN_pos hN_le
    by_contra! h_gt
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_gt
    have hT_G : ∀ l ∈ T, l ∈ G_q ∧ l ∣ N := by
      intro l hl
      exact Finset.mem_filter.mp (hT_sub hl)
    have hT_prime : ∀ l ∈ T, q / 64 + 1 ≤ l ∧ Nat.Prime l := by
      intro l hl
      have hl_mem := hG_sub (hT_G l hl).1
      rw [Finset.mem_filter, Finset.mem_Ioc] at hl_mem
      exact ⟨by omega, hl_mem.2⟩
    have h_prod_dvd : (∏ l ∈ T, l) ∣ N := by
      rw [← Int.natCast_dvd_natCast, Nat.cast_prod]
      apply Finset.prod_dvd_of_coprime
      · intro l₁ hl₁ l₂ hl₂ hne
        exact ((Nat.coprime_primes (hT_prime l₁ hl₁).2 (hT_prime l₂ hl₂).2).mpr hne).isCoprime
      · intro l hl
        exact Int.natCast_dvd_natCast.mpr (hT_G l hl).2
    have h_prod_le_N : (∏ l ∈ T, l) ≤ N := Nat.le_of_dvd hN_pos h_prod_dvd
    have hT_card3 : T.card = 3 := hT_card
    have h_pow_le_prod : (q / 64 + 1) ^ 3 ≤ ∏ l ∈ T, l := by
      rw [← hT_card3]
      exact Finset.pow_card_le_prod T id (q / 64 + 1) (fun l hl => (hT_prime l hl).1)
    have h_cube_le : (q / 64 + 1) ^ 3 ≤ q ^ 2 / 4 := le_trans h_pow_le_prod (le_trans h_prod_le_N hN_le)
    have h1 : q < 64 * (q / 64 + 1) := by omega
    have h_pow3 : q ^ 3 < (64 * (q / 64 + 1)) ^ 3 := Nat.pow_lt_pow_left h1 (by decide)
    have h_q2_4 : 4 * (q ^ 2 / 4) ≤ q ^ 2 := Nat.mul_div_le (q ^ 2) 4
    nlinarith

  have h_fiber : ∀ c ∈ G_q.image c_of, (G_q.filter (fun l => c_of l = c)).card ≤ 4 := by
    intro c hc
    obtain ⟨l₀, hl₀_G, rfl⟩ := Finset.mem_image.mp hc
    have hl₀_props := hG_props l₀ hl₀_G
    have hl₀_mem := hG_sub hl₀_G
    rw [Finset.mem_filter, Finset.mem_Ioc] at hl₀_mem
    have hc_ge1 : 1 ≤ c_of l₀ := hl₀_props.1
    have hc_lt_q4 : c_of l₀ < q / 4 := lt_of_lt_of_le hl₀_props.2.1 hl₀_mem.1.2
    have h4c : 4 * (c_of l₀ + 1) ≤ q := by omega
    set N₁ := q * c_of l₀ + 1
    set N₂ := q * c_of l₀ - 1
    have hN₁_pos : 1 ≤ N₁ := by omega
    have hN₁_le : N₁ ≤ q ^ 2 / 4 := by
      have : 4 * (q * c_of l₀ + 1) ≤ q ^ 2 := by nlinarith
      omega
    have hN₂_pos : 1 ≤ N₂ := by
      have : q ≤ q * c_of l₀ := Nat.le_mul_of_pos_right q (by omega)
      omega
    have hN₂_le : N₂ ≤ q ^ 2 / 4 := by omega
    have h_sub_union : G_q.filter (fun l => c_of l = c_of l₀) ⊆
        (G_q.filter (fun l => l ∣ N₁)) ∪ (G_q.filter (fun l => l ∣ N₂)) := by
      intro l hl
      rw [Finset.mem_filter] at hl
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases (hG_props l hl.1).2.2.2.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        refine ⟨hl.1, d_of l, ?_⟩
        rw [hl.2] at h1
        dsimp [N₁]
        omega
      · right
        refine ⟨hl.1, d_of l, ?_⟩
        rw [hl.2] at h1
        dsimp [N₂]
        omega
    have h_card_union := le_trans (Finset.card_le_card h_sub_union) (Finset.card_union_le _ _)
    have h1 := h_div_card N₁ hN₁_pos hN₁_le
    have h2 := h_div_card N₂ hN₂_pos hN₂_le
    omega

  have hG_le_4C : G_q.card ≤ 4 * (G_q.image c_of).card :=
    Finset.card_le_mul_card_image G_q 4 h_fiber
  have hL_ge : 128 ≤ Nat.log 2 q := by
    have h1 : Nat.log 2 (2 ^ 128) ≤ Nat.log 2 q := Nat.log_mono_right (le_of_lt hq)
    rwa [Nat.log_pow (by decide : 1 < 2)] at h1
  have h2L_le : 2 ^ (Nat.log 2 q) ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hx_lt : Nat.log 2 q - 32 < 2 ^ (Nat.log 2 q - 32) := Nat.lt_two_pow_self
  have h2x : 2 ^ 32 * 2 ^ (Nat.log 2 q - 32) ≤ q := by
    rw [← Nat.pow_add]
    have h_eq : 32 + (Nat.log 2 q - 32) = Nat.log 2 q := by omega
    rw [h_eq]
    exact h2L_le
  set K := Nat.log 2 q + 1
  set C_q := G_q.image c_of
  set M_low := q / (1024 * K)
  set C_high := C_q.filter (fun c => M_low ≤ c)
  have h_sdiff_sub : C_q.filter (fun c => ¬ M_low ≤ c) ⊆ Finset.range M_low := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_range]
    omega
  have h_sdiff_card : (C_q.filter (fun c => ¬ M_low ≤ c)).card ≤ M_low := by
    simpa using Finset.card_le_card h_sdiff_sub
  have h_part : C_high.card + (C_q.filter (fun c => ¬ M_low ≤ c)).card = C_q.card :=
    Finset.card_filter_add_card_filter_not (s := C_q) (p := fun c => M_low ≤ c)
  set m := q / (512 * K)
  have hm_16 : 16 * m ≤ q / (32 * K) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : (512 * K) * m ≤ q := Nat.mul_div_le q (512 * K)
    linarith
  have hm_low : M_low ≤ m := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : (1024 * K) * M_low ≤ q := Nat.mul_div_le q (1024 * K)
    linarith
  have hm_512 : 512 ≤ m := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hm_le_Chigh : m ≤ C_high.card := by omega
  let eqv : Fin C_high.card ≃ {c // c ∈ C_high} := C_high.equivFin.symm
  have h_pre : ∀ c : {c // c ∈ C_high}, ∃ l ∈ G_q, c_of l = c.1 := by
    intro c
    have hc_mem := (Finset.mem_filter.mp c.2).1
    exact Finset.mem_image.mp hc_mem
  let idx : ℕ → ℕ := fun j =>
    if hj : j < m then
      Classical.choose (h_pre (eqv ⟨j, lt_of_lt_of_le hj hm_le_Chigh⟩))
    else 0
  have h_idx_mem : ∀ j < m, idx j ∈ G_q ∧ M_low ≤ c_of (idx j) := by
    intro j hj
    have h_idx_eq : idx j = Classical.choose (h_pre (eqv ⟨j, lt_of_lt_of_le hj hm_le_Chigh⟩)) := dif_pos hj
    have h_spec := Classical.choose_spec (h_pre (eqv ⟨j, lt_of_lt_of_le hj hm_le_Chigh⟩))
    rw [h_idx_eq]
    refine ⟨h_spec.1, ?_⟩
    rw [h_spec.2]
    exact (Finset.mem_filter.mp (eqv ⟨j, lt_of_lt_of_le hj hm_le_Chigh⟩).2).2
  have h_idx_inj : ∀ j₁ < m, ∀ j₂ < m, j₁ ≠ j₂ → c_of (idx j₁) ≠ c_of (idx j₂) := by
    intro j₁ hj₁ j₂ hj₂ hne h_eq
    have h_idx1 : idx j₁ = Classical.choose (h_pre (eqv ⟨j₁, lt_of_lt_of_le hj₁ hm_le_Chigh⟩)) := dif_pos hj₁
    have h_idx2 : idx j₂ = Classical.choose (h_pre (eqv ⟨j₂, lt_of_lt_of_le hj₂ hm_le_Chigh⟩)) := dif_pos hj₂
    have h_spec1 := (Classical.choose_spec (h_pre (eqv ⟨j₁, lt_of_lt_of_le hj₁ hm_le_Chigh⟩))).2
    have h_spec2 := (Classical.choose_spec (h_pre (eqv ⟨j₂, lt_of_lt_of_le hj₂ hm_le_Chigh⟩))).2
    rw [h_idx1] at h_eq
    rw [h_idx2] at h_eq
    rw [h_spec1, h_spec2] at h_eq
    have h_sub_eq : eqv ⟨j₁, lt_of_lt_of_le hj₁ hm_le_Chigh⟩ = eqv ⟨j₂, lt_of_lt_of_le hj₂ hm_le_Chigh⟩ :=
      Subtype.ext h_eq
    have h_fin_eq := eqv.injective h_sub_eq
    exact hne (Fin.ext_iff.mp h_fin_eq)

  
  have h_pair_1 : ∀ c l d a : ℕ,
      q / (1024 * (Nat.log 2 q + 1)) ≤ c →
      c < q / 4 →
      Nat.Coprime c p →
      1 ≤ l → l ≤ q →
      1 ≤ d → d ≤ q →
      Nat.Coprime l d →
      ((a = q * c ∧ a + 1 = l * d) ∨ (a + 1 = q * c ∧ a = l * d)) →
      q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ a ∧
      a + 1 ≤ q ^ 2 / 2 ∧
      w_Icc a (a + 1) ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2 ∧
      q ∣ a * (a + 1) ∧
      ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a (a + 1)).den = 1 ∧
      ((p : ℤ) ∣ ((c : ℤ) * ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a (a + 1)).num -
        (((Finset.Icc 1 q).lcm id / q : ℕ) : ℤ))) := by
    intro c l d a hc_low hc_high hc_cop hl_ge1 hl_le_q hd_ge1 hd_le_q hld_cop ha_rel
    have hM_small : 4 * (1024 * (Nat.log 2 q + 1)) ≤ q := by omega
    have hM_pos : 0 < 1024 * (Nat.log 2 q + 1) := by omega
    have hqM_pos : 1 ≤ q / (1024 * (Nat.log 2 q + 1)) := Nat.div_pos (by omega) hM_pos
    have hc_ge1 : 1 ≤ c := le_trans hqM_pos hc_low
    have h_div_mod := Nat.div_add_mod q (1024 * (Nat.log 2 q + 1))
    have h_mod_lt : q % (1024 * (Nat.log 2 q + 1)) < 1024 * (Nat.log 2 q + 1) := Nat.mod_lt q hM_pos
    have hMc_le : (1024 * (Nat.log 2 q + 1)) * (q / (1024 * (Nat.log 2 q + 1))) ≤
        (1024 * (Nat.log 2 q + 1)) * c := Nat.mul_le_mul_left _ hc_low
    have ha_ge_qc : q * c ≤ a + 1 := by
      rcases ha_rel with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have ha_le_qc : a ≤ q * c := by
      rcases ha_rel with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have h_q2_le : q ^ 2 ≤ (2048 * (Nat.log 2 q + 1)) * a := by nlinarith
    have ha_bound1 : q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ a := Nat.div_le_of_le_mul h_q2_le
    have ha_bound2 : a + 1 ≤ q ^ 2 / 2 := by
      have h4c : 4 * c < q := by omega
      have h2a : 2 * (a + 1) ≤ q ^ 2 := by nlinarith
      omega
    have ha_pos : 0 < a := by nlinarith
    have hw_eq : w_Icc a (a + 1) = (a : ℚ)⁻¹ + ((a + 1 : ℕ) : ℚ)⁻¹ := by
      unfold w_Icc
      have h_icc : Finset.Icc a (a + 1) = {a, a + 1} := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [h_icc, Finset.sum_pair (by omega)]
    have hw_bound : w_Icc a (a + 1) ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2 := by
      rw [hw_eq]
      have ha_q_pos : (0 : ℚ) < (a : ℚ) := Nat.cast_pos.mpr ha_pos
      have h_inv_le : ((a + 1 : ℕ) : ℚ)⁻¹ ≤ (a : ℚ)⁻¹ := by
        apply inv_anti₀ ha_q_pos
        exact_mod_cast (by omega : a ≤ a + 1)
      have h_sum_le : (a : ℚ)⁻¹ + ((a + 1 : ℕ) : ℚ)⁻¹ ≤ 2 / (a : ℚ) := by
        linarith [div_eq_mul_inv (2 : ℚ) (a : ℚ)]
      have h_q2_q : (q : ℚ) ^ 2 ≤ (2048 * (Nat.log 2 q + 1) : ℚ) * (a : ℚ) := by
        exact_mod_cast h_q2_le
      have h_div_le : 2 / (a : ℚ) ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2 := by
        rw [div_le_div_iff₀ ha_q_pos (by positivity)]
        linarith
      exact le_trans h_sum_le h_div_le
    have hq_dvd_prod : q ∣ a * (a + 1) := by
      rcases ha_rel with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1, mul_assoc]
        exact dvd_mul_right q _
      · rw [h1, mul_comm a (q * c), mul_assoc]
        exact dvd_mul_right q _
    have hq_dvd_D : q ∣ (Finset.Icc 1 q).lcm id := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, le_refl q⟩)
    have hc_dvd_D : c ∣ (Finset.Icc 1 q).lcm id := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hc_ge1, by omega⟩)
    have hl_dvd_D : l ∣ (Finset.Icc 1 q).lcm id := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hl_ge1, hl_le_q⟩)
    have hd_dvd_D : d ∣ (Finset.Icc 1 q).lcm id := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hd_ge1, hd_le_q⟩)
    have hqc_cop : Nat.Coprime q c := by
      rw [hq_eq]
      exact (hc_cop.pow_right e).symm
    have hqc_dvd_D : q * c ∣ (Finset.Icc 1 q).lcm id := hqc_cop.mul_dvd_of_dvd_of_dvd hq_dvd_D hc_dvd_D
    have hld_dvd_D : l * d ∣ (Finset.Icc 1 q).lcm id := hld_cop.mul_dvd_of_dvd_of_dvd hl_dvd_D hd_dvd_D
    have hD_u : (q * c) * ((Finset.Icc 1 q).lcm id / (q * c)) = (Finset.Icc 1 q).lcm id :=
      Nat.mul_div_cancel' hqc_dvd_D
    have hD_v : (l * d) * ((Finset.Icc 1 q).lcm id / (l * d)) = (Finset.Icc 1 q).lcm id :=
      Nat.mul_div_cancel' hld_dvd_D
    have hqc_pos : 0 < q * c := Nat.mul_pos (by omega) hc_ge1
    have hld_pos : 0 < l * d := Nat.mul_pos hl_ge1 hd_ge1
    have hw_alt : w_Icc a (a + 1) = ((q * c : ℕ) : ℚ)⁻¹ + ((l * d : ℕ) : ℚ)⁻¹ := by
      rw [hw_eq]
      rcases ha_rel with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, h1]
      · rw [h1, h2, add_comm]
    have hDw_eq : (((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a (a + 1) =
        ((((Finset.Icc 1 q).lcm id / (q * c) + (Finset.Icc 1 q).lcm id / (l * d) : ℕ) : ℚ)) := by
      rw [hw_alt, mul_add]
      have h1 : (((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * ((q * c : ℕ) : ℚ)⁻¹ =
          (((Finset.Icc 1 q).lcm id / (q * c) : ℕ) : ℚ) := by
        have hD_cast : (((Finset.Icc 1 q).lcm id : ℕ) : ℚ) =
            ((q * c : ℕ) : ℚ) * (((Finset.Icc 1 q).lcm id / (q * c) : ℕ) : ℚ) := by
          exact_mod_cast hD_u.symm
        rw [hD_cast, mul_comm (((q * c : ℕ) : ℚ)), mul_assoc,
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt hqc_pos)), mul_one]
      have h2 : (((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * ((l * d : ℕ) : ℚ)⁻¹ =
          (((Finset.Icc 1 q).lcm id / (l * d) : ℕ) : ℚ) := by
        have hD_cast : (((Finset.Icc 1 q).lcm id : ℕ) : ℚ) =
            ((l * d : ℕ) : ℚ) * (((Finset.Icc 1 q).lcm id / (l * d) : ℕ) : ℚ) := by
          exact_mod_cast hD_v.symm
        rw [hD_cast, mul_comm (((l * d : ℕ) : ℚ)), mul_assoc,
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt hld_pos)), mul_one]
      rw [h1, h2, Nat.cast_add]
    have h_den : ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a (a + 1)).den = 1 := by
      rw [hDw_eq, Rat.den_natCast]
    have h_num : ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a (a + 1)).num =
        (((Finset.Icc 1 q).lcm id / (q * c) + (Finset.Icc 1 q).lcm id / (l * d) : ℕ) : ℤ) := by
      rw [hDw_eq, Rat.num_natCast]
    have hDq_eq : (Finset.Icc 1 q).lcm id / q = c * ((Finset.Icc 1 q).lcm id / (q * c)) := by
      have h_assoc : q * (c * ((Finset.Icc 1 q).lcm id / (q * c))) = (Finset.Icc 1 q).lcm id := by
        linarith [hD_u]
      calc (Finset.Icc 1 q).lcm id / q
          = (q * (c * ((Finset.Icc 1 q).lcm id / (q * c)))) / q := by rw [h_assoc]
        _ = c * ((Finset.Icc 1 q).lcm id / (q * c)) := Nat.mul_div_right _ (by omega)
    have h_diff_eq : (c : ℤ) * ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a (a + 1)).num -
        (((Finset.Icc 1 q).lcm id / q : ℕ) : ℤ) =
        (c : ℤ) * (((Finset.Icc 1 q).lcm id / (l * d) : ℕ) : ℤ) := by
      rw [h_num, hDq_eq]
      push_cast
      ring
    have hp_dvd_q : p ∣ q := by
      rw [hq_eq]
      exact dvd_pow_self p (by omega)
    have hp_dvd_D : p ∣ (Finset.Icc 1 q).lcm id := dvd_trans hp_dvd_q hq_dvd_D
    have hp_not_dvd_ld : ¬ p ∣ l * d := by
      intro h_dvd
      have hp_dvd_qc : p ∣ q * c := dvd_mul_of_dvd_left hp_dvd_q c
      have hp_dvd_one : p ∣ 1 := by
        rcases ha_rel with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have h_eq : q * c + 1 = l * d := by omega
          rw [← h_eq] at h_dvd
          exact (Nat.dvd_add_right hp_dvd_qc).mp h_dvd
        · have h_eq : l * d + 1 = q * c := by omega
          rw [← h_eq] at hp_dvd_qc
          exact (Nat.dvd_add_right h_dvd).mp hp_dvd_qc
      exact hp.not_dvd_one hp_dvd_one
    have hp_dvd_v : p ∣ (Finset.Icc 1 q).lcm id / (l * d) := by
      rw [← hD_v] at hp_dvd_D
      exact (hp.dvd_or_dvd hp_dvd_D).resolve_left hp_not_dvd_ld
    have hp_dvd_diff : (p : ℤ) ∣ ((c : ℤ) * ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a (a + 1)).num -
        (((Finset.Icc 1 q).lcm id / q : ℕ) : ℤ)) := by
      rw [h_diff_eq]
      have hp_v_z : (p : ℤ) ∣ (((Finset.Icc 1 q).lcm id / (l * d) : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hp_dvd_v
      exact dvd_mul_of_dvd_right hp_v_z (c : ℤ)
    exact ⟨ha_bound1, ha_bound2, hw_bound, hq_dvd_prod, h_den, hp_dvd_diff⟩

  have h_pair_2 : ∀ c₁ c₂ a₁ a₂ : ℕ,
      1 ≤ c₁ → 1 ≤ c₂ → c₁ ≠ c₂ →
      (a₁ = q * c₁ ∨ a₁ + 1 = q * c₁) →
      (a₂ = q * c₂ ∨ a₂ + 1 = q * c₂) →
      (a₁ + 1) + 1 < a₂ ∨ (a₂ + 1) + 1 < a₁ := by
    intro c₁ c₂ a₁ a₂ hc₁ hc₂ hne ha₁ ha₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have h_le : c₁ + 1 ≤ c₂ := hlt
      have h_mul : q * (c₁ + 1) ≤ q * c₂ := Nat.mul_le_mul_left q h_le
      have h_expand : q * c₁ + q ≤ q * c₂ := by linarith
      omega
    · right
      have h_le : c₂ + 1 ≤ c₁ := hgt
      have h_mul : q * (c₂ + 1) ≤ q * c₁ := Nat.mul_le_mul_left q h_le
      have h_expand : q * c₂ + q ≤ q * c₁ := by linarith
      omega

  let I : ℕ → ℕ × ℕ := fun j => (a_of (idx j), a_of (idx j) + 1)
  let c : ℕ → ℕ := fun j => c_of (idx j)
  refine ⟨I, c, ?_, ?_⟩
  · intro j hj
    obtain ⟨hl_G, hc_low⟩ := h_idx_mem j hj
    obtain ⟨hc_ge1, hc_lt_l, hc_cop, hd_ge1, hd_lt_q, hld_cop, ha_rel⟩ := hG_props (idx j) hl_G
    have hl_mem := hG_sub hl_G
    rw [Finset.mem_filter, Finset.mem_Ioc] at hl_mem
    have hl_gt : q / 64 < idx j := hl_mem.1.1
    have hl_le : idx j ≤ q / 4 := hl_mem.1.2
    have hc_lt_q4 : c j < q / 4 := lt_of_lt_of_le hc_lt_l hl_le
    have hl_ge1 : 1 ≤ idx j := by omega
    have hl_le_q : idx j ≤ q := by omega
    have hd_le_q : d_of (idx j) ≤ q := by omega
    obtain ⟨ha_low, ha_high, hw_le, hq_dvd, h_den, h_mod⟩ :=
      h_pair_1 (c j) (idx j) (d_of (idx j)) (a_of (idx j))
        hc_low hc_lt_q4 hc_cop hl_ge1 hl_le_q hd_ge1 hd_le_q hld_cop ha_rel
    exact ⟨hc_low, hc_lt_q4, hc_cop, ha_low, rfl, ha_high, hw_le, hq_dvd, h_den, h_mod⟩
  · intro j₁ hj₁ j₂ hj₂ hne
    have hc_ne : c j₁ ≠ c j₂ := h_idx_inj j₁ hj₁ j₂ hj₂ hne
    obtain ⟨hl₁, _⟩ := h_idx_mem j₁ hj₁
    obtain ⟨hl₂, _⟩ := h_idx_mem j₂ hj₂
    obtain ⟨hc₁_ge1, _, _, _, _, _, ha₁_rel⟩ := hG_props (idx j₁) hl₁
    obtain ⟨hc₂_ge1, _, _, _, _, _, ha₂_rel⟩ := hG_props (idx j₂) hl₂
    have ha₁_or : a_of (idx j₁) = q * c j₁ ∨ a_of (idx j₁) + 1 = q * c j₁ := by
      rcases ha₁_rel with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    have ha₂_or : a_of (idx j₂) = q * c j₂ ∨ a_of (idx j₂) + 1 = q * c j₂ := by
      rcases ha₂_rel with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    refine ⟨hc_ne, ?_⟩
    exact h_pair_2 (c j₁) (c j₂) (a_of (idx j₁)) (a_of (idx j₂)) hc₁_ge1 hc₂_ge1 hc_ne ha₁_or ha₂_or

theorem inverse_residue_phase_distribution_bound (q p e : ℕ)
    (hq : 2 ^ 128 < q) (hp : Nat.Prime p) (he : 1 ≤ e) (hq_eq : q = p ^ e)
    (hD_step : (Finset.Icc 1 q).lcm id = p * (Finset.Icc 1 (q - 1)).lcm id)
    (hL_step : ((Finset.Icc 1 q).lcm id) / 1189 = p * (((Finset.Icc 1 (q - 1)).lcm id) / 1189))
    (hL_prev : 1189 * (((Finset.Icc 1 (q - 1)).lcm id) / 1189) = (Finset.Icc 1 (q - 1)).lcm id)
    (hL_curr : 1189 * (((Finset.Icc 1 q).lcm id) / 1189) = (Finset.Icc 1 q).lcm id)
    (h_cop_Dq : Nat.Coprime p (((Finset.Icc 1 q).lcm id) / q))
    (I : ℕ → ℕ × ℕ) (c : ℕ → ℕ)
    (hc_props : ∀ j < q / (512 * (Nat.log 2 q + 1)),
      c j < q / 4 ∧
      Nat.Coprime (c j) p ∧
      ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).den = 1 ∧
      ((p : ℤ) ∣ ((c j : ℤ) * ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).num -
        (((Finset.Icc 1 q).lcm id / q : ℕ) : ℤ))))
    (hc_inj : ∀ j₁ < q / (512 * (Nat.log 2 q + 1)), ∀ j₂ < q / (512 * (Nat.log 2 q + 1)),
      j₁ ≠ j₂ → c j₁ ≠ c j₂) :
    ∃ Δ_q : Finset ℤ, Δ_q.card ≤ q ∧
      (∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        ∃ δ₀ ∈ Δ_q, ∀ j < q / (512 * (Nat.log 2 q + 1)),
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ)))) ^ 2 =
          (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ)))) ^ 2) ∧
      (∀ δ₀ ∈ Δ_q, ∀ U ⊆ Finset.range (q / (512 * (Nat.log 2 q + 1))),
        (q / (512 * (Nat.log 2 q + 1))) / 2048 ≤ U.card →
        7 * U.card / 8 ≤
          (U.filter (fun j =>
            (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
              (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ)))) ^ 2)).card) :=
by
  classical
  set D_q : ℕ := (Finset.Icc 1 q).lcm id
  set D_q1 : ℕ := (Finset.Icc 1 (q - 1)).lcm id
  set L_q1 : ℕ := D_q1 / 1189
  have h_s1 :
      (∀ (w : ℚ) (k : ℤ),
        (((D_q : ℕ) : ℚ) * w).den = 1 →
        (Real.sin (Real.pi * (((k * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w : ℝ))))) ^ 2 =
        (Real.sin (Real.pi * (((((k * (((D_q : ℕ) : ℚ) * w).num) % (p : ℤ)).toNat : ℕ) : ℝ) / (p : ℝ)))) ^ 2) ∧
      (∀ δ : ℤ,
        (L_q1 : ℤ) ∣ δ →
        ¬ (((p * L_q1 : ℕ) : ℤ) ∣ δ) →
        ∃ a ∈ Finset.Ico 1 p,
          ∀ w : ℚ, (((D_q : ℕ) : ℚ) * w).den = 1 →
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w : ℝ)))) ^ 2 =
            (Real.sin (Real.pi * ((((a : ℤ) * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w : ℝ))))) ^ 2) := by
    have hp_pos : 0 < p := hp.pos
    have hp_ge2 : 2 ≤ p := hp.two_le
    have hp_ne_r : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hp_ne_z : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have h_part1 : ∀ (w : ℚ) (k : ℤ),
        (((D_q : ℕ) : ℚ) * w).den = 1 →
        (Real.sin (Real.pi * (((k * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w : ℝ))))) ^ 2 =
        (Real.sin (Real.pi * (((((k * (((D_q : ℕ) : ℚ) * w).num) % (p : ℤ)).toNat : ℕ) : ℝ) / (p : ℝ)))) ^ 2 := by
      intro w k h_den
      set W : ℤ := (((D_q : ℕ) : ℚ) * w).num
      have hW_q : (W : ℚ) = (D_q : ℚ) * w := (Rat.den_eq_one_iff (((D_q : ℕ) : ℚ) * w)).mp h_den
      have hW_r : (W : ℝ) = (D_q : ℝ) * (w : ℝ) := by exact_mod_cast hW_q
      have hDq_r : (D_q : ℝ) = (p : ℝ) * (1189 * (L_q1 : ℝ)) := by
        have h1 : D_q = p * (1189 * L_q1) := by rw [hD_step, ← hL_prev]
        exact_mod_cast h1
      have h_arg_eq : ((k * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w : ℝ)) = ((k * W : ℤ) : ℝ) / (p : ℝ) := by
        push_cast
        rw [hW_r, hDq_r]
        field_simp [hp_ne_r]
      set z : ℕ := ((k * W) % (p : ℤ)).toNat
      set t : ℤ := (k * W) / (p : ℤ)
      have hz_nonneg : 0 ≤ (k * W) % (p : ℤ) := Int.emod_nonneg _ hp_ne_z
      have hz_z : (z : ℤ) = (k * W) % (p : ℤ) := Int.toNat_of_nonneg hz_nonneg
      have h_div_mod : (z : ℤ) + (p : ℤ) * t = k * W := by
        rw [hz_z]
        exact Int.emod_add_mul_ediv (k * W) (p : ℤ)
      have h_div_mod_r : (z : ℝ) + (p : ℝ) * (t : ℝ) = ((k * W : ℤ) : ℝ) := by
        exact_mod_cast h_div_mod
      have h_pi_split : Real.pi * (((k * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w : ℝ))) =
          Real.pi * ((z : ℝ) / (p : ℝ)) + (t : ℝ) * Real.pi := by
        rw [h_arg_eq, ← h_div_mod_r]
        field_simp [hp_ne_r]
      rw [h_pi_split, Real.sin_add_int_mul_pi]
      have h_abs : |(-1 : ℝ) ^ t| = 1 := by simp [abs_zpow]
      have h_sq_neg1 : ((-1 : ℝ) ^ t) ^ 2 = 1 := by
        rw [← sq_abs, h_abs, one_pow]
      calc ((-1 : ℝ) ^ t * Real.sin (Real.pi * ((z : ℝ) / (p : ℝ)))) ^ 2
          = ((-1 : ℝ) ^ t) ^ 2 * (Real.sin (Real.pi * ((z : ℝ) / (p : ℝ)))) ^ 2 := mul_pow _ _ 2
        _ = (Real.sin (Real.pi * ((z : ℝ) / (p : ℝ)))) ^ 2 := by rw [h_sq_neg1, one_mul]
    refine ⟨h_part1, ?_⟩
    intro δ h_dvd h_not_dvd
    obtain ⟨k, rfl⟩ := h_dvd
    set a : ℕ := (k % (p : ℤ)).toNat
    have hk_nonneg : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ hp_ne_z
    have ha_z : (a : ℤ) = k % (p : ℤ) := Int.toNat_of_nonneg hk_nonneg
    have hk_lt : k % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos k (by omega)
    have ha_lt_p : a < p := by omega
    have ha_ne0 : a ≠ 0 := by
      intro ha0
      apply h_not_dvd
      have hk_mod0 : k % (p : ℤ) = 0 := by omega
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero hk_mod0
      refine ⟨m, ?_⟩
      push_cast
      rw [hm]
      ring
    refine ⟨a, Finset.mem_Ico.mpr ⟨by omega, ha_lt_p⟩, fun w h_den => ?_⟩
    have h1 := h_part1 w k h_den
    have h2 := h_part1 w (a : ℤ) h_den
    have h_δ_eq : Real.pi * (((L_q1 : ℤ) * k : ℤ) : ℝ) * (1189 * (w : ℝ)) =
        Real.pi * (((k * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w : ℝ))) := by
      push_cast
      ring
    rw [h_δ_eq, h1, h2]
    have h_mod_eq : ((a : ℤ) * (((D_q : ℕ) : ℚ) * w).num) % (p : ℤ) =
        (k * (((D_q : ℕ) : ℚ) * w).num) % (p : ℤ) := by
      rw [Int.mul_emod, ha_z, Int.emod_emod, ← Int.mul_emod]
    rw [h_mod_eq]

  have h_s2 : ∀ (z : ℕ),
      p / (2 ^ 25 * (Nat.log 2 q + 1)) + 1 ≤ z →
      z + (p / (2 ^ 25 * (Nat.log 2 q + 1)) + 1) ≤ p →
      (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
        (Real.sin (Real.pi * ((z : ℝ) / (p : ℝ)))) ^ 2 := by
    intro z hz_low hz_high
    set M : ℕ := 2 ^ 25 * (Nat.log 2 q + 1)
    set B : ℕ := p / M
    change B + 1 ≤ z at hz_low
    change z + (B + 1) ≤ p at hz_high
    have hM_pos : 0 < M := by positivity
    have hp_r_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hM_r_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    have hp_lt_MB1 : p < M * (B + 1) := by
      have h_div : M * B + p % M = p := Nat.div_add_mod p M
      have h_mod : p % M < M := Nat.mod_lt p hM_pos
      calc p = M * B + p % M := h_div.symm
        _ < M * B + M := Nat.add_lt_add_left h_mod (M * B)
        _ = M * (B + 1) := by ring
    have hp_le_Mz : p ≤ M * z := le_trans (le_of_lt hp_lt_MB1) (Nat.mul_le_mul_left M hz_low)
    have hpz_ge : B + 1 ≤ p - z := Nat.le_sub_of_add_le' hz_high
    have hp_le_Mpz : p ≤ M * (p - z) := le_trans (le_of_lt hp_lt_MB1) (Nat.mul_le_mul_left M hpz_ge)
    have hz_le_p : z ≤ p := Nat.le_of_add_right_le hz_high
    set x : ℝ := (z : ℝ) / (p : ℝ)
    have hx_low : 1 / (M : ℝ) ≤ x := by
      rw [div_le_div_iff₀ hM_r_pos hp_r_pos]
      have : (p : ℝ) ≤ (M : ℝ) * (z : ℝ) := by exact_mod_cast hp_le_Mz
      linarith
    have hx_high : 1 / (M : ℝ) ≤ 1 - x := by
      have h_sub : 1 - x = ((p - z : ℕ) : ℝ) / (p : ℝ) := by
        dsimp [x]
        rw [Nat.cast_sub hz_le_p]
        field_simp [ne_of_gt hp_r_pos]
      rw [h_sub, div_le_div_iff₀ hM_r_pos hp_r_pos]
      have : (p : ℝ) ≤ (M : ℝ) * ((p - z : ℕ) : ℝ) := by exact_mod_cast hp_le_Mpz
      linarith
    set u : ℝ := min x (1 - x)
    have hu_ge : 1 / (M : ℝ) ≤ u := le_min hx_low hx_high
    have hu_pos : 0 ≤ u := le_trans (by positivity) hu_ge
    have hu_le_half : u ≤ 1 / 2 := by
      have h1 : u ≤ x := min_le_left _ _
      have h2 : u ≤ 1 - x := min_le_right _ _
      linarith
    have hpi_u_pos : 0 ≤ Real.pi * u := mul_nonneg Real.pi_nonneg hu_pos
    have hpi_u_le : Real.pi * u ≤ Real.pi / 2 := by
      have := mul_le_mul_of_nonneg_left hu_le_half Real.pi_nonneg
      linarith
    have h_jordan := Real.mul_le_sin hpi_u_pos hpi_u_le
    have h_two_u : (2 / Real.pi) * (Real.pi * u) = 2 * u := by
      field_simp [Real.pi_ne_zero]
    rw [h_two_u] at h_jordan
    have h_sin_eq : Real.sin (Real.pi * x) = Real.sin (Real.pi * u) := by
      dsimp [u]
      rcases min_cases x (1 - x) with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
      · rw [h_eq]
      · rw [h_eq]
        have h_pi_sub : Real.pi * x = Real.pi - Real.pi * (1 - x) := by ring
        rw [h_pi_sub, Real.sin_pi_sub]
    have h_sin_ge : 2 / (M : ℝ) ≤ Real.sin (Real.pi * x) := by
      rw [h_sin_eq]
      have h_two_div : 2 / (M : ℝ) = 2 * (1 / (M : ℝ)) := by ring
      linarith
    have h_lhs_pos : 0 ≤ 2 / (M : ℝ) := by positivity
    have h_sq : (2 / (M : ℝ)) ^ 2 ≤ (Real.sin (Real.pi * x)) ^ 2 := by
      nlinarith
    have h_M_eq : (2 / (M : ℝ)) ^ 2 = (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) := by
      have hM_cast : (M : ℝ) = 2 ^ 25 * (Nat.log 2 q + 1 : ℝ) := by
        dsimp [M]
        push_cast
        ring
      rw [hM_cast]
      field_simp
    linarith

  have h_s3 : ∀ (D_q' a : ℕ),
      Nat.Coprime p D_q' →
      1 ≤ a → a < p →
      ∀ (W : ℕ → ℤ),
      (∀ j < q / (512 * (Nat.log 2 q + 1)),
        c j < q / 4 ∧ ((p : ℤ) ∣ ((c j : ℤ) * W j - (D_q' : ℤ)))) →
      ∀ (U : Finset ℕ), U ⊆ Finset.range (q / (512 * (Nat.log 2 q + 1))) →
      (q / (512 * (Nat.log 2 q + 1))) / 2048 ≤ U.card →
      7 * U.card / 8 ≤
        (U.filter (fun j =>
          p / (2 ^ 25 * (Nat.log 2 q + 1)) + 1 ≤ (((a : ℤ) * W j) % (p : ℤ)).toNat ∧
          (((a : ℤ) * W j) % (p : ℤ)).toNat + (p / (2 ^ 25 * (Nat.log 2 q + 1)) + 1) ≤ p)).card := by
    intro D_q' a h_cop_Dq' ha_low ha_high W hc_props_W U hU_sub hU_card
    have h_core : ∀ (m B : ℕ),
        (∀ j < m, c j < q / 4 ∧ ((p : ℤ) ∣ ((c j : ℤ) * W j - (D_q' : ℤ)))) →
        (∀ j₁ < m, ∀ j₂ < m, j₁ ≠ j₂ → c j₁ ≠ c j₂) →
        U ⊆ Finset.range m →
        2 * (B * (q / p)) ≤ U.card / 8 →
        7 * U.card / 8 ≤
          (U.filter (fun j =>
            B + 1 ≤ (((a : ℤ) * W j) % (p : ℤ)).toNat ∧
            (((a : ℤ) * W j) % (p : ℤ)).toNat + (B + 1) ≤ p)).card := by
      intro m B hc_props_m hc_inj_m hU_sub_m h_2B_le
      let z : ℕ → ℕ := fun j => (((a : ℤ) * W j) % (p : ℤ)).toNat
      have hp_pos : 0 < p := hp.pos
      have hp_ne_z : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hp_dvd_q : p ∣ q := by
        rw [hq_eq]
        exact dvd_pow_self p (by omega : e ≠ 0)
      have h_p_mul_qp : p * (q / p) = q := Nat.mul_div_cancel' hp_dvd_q
      have hz_props : ∀ j < m,
          1 ≤ z j ∧ z j < p ∧ (p : ℤ) ∣ ((c j : ℤ) * (z j : ℤ) - (a : ℤ) * (D_q' : ℤ)) := by
        intro j hj
        have hz_nonneg : 0 ≤ ((a : ℤ) * W j) % (p : ℤ) := Int.emod_nonneg _ hp_ne_z
        have hz_z : (z j : ℤ) = ((a : ℤ) * W j) % (p : ℤ) := Int.toNat_of_nonneg hz_nonneg
        have hz_lt_z : ((a : ℤ) * W j) % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ (by omega)
        have hz_lt_p : z j < p := by omega
        have h_ediv := Int.emod_add_mul_ediv ((a : ℤ) * W j) (p : ℤ)
        rw [← hz_z] at h_ediv
        obtain ⟨t2, ht2⟩ := (hc_props_m j hj).2
        have h_rel : (p : ℤ) ∣ ((c j : ℤ) * (z j : ℤ) - (a : ℤ) * (D_q' : ℤ)) := by
          refine ⟨(c j : ℤ) * (- (((a : ℤ) * W j) / (p : ℤ))) + (a : ℤ) * t2, ?_⟩
          linear_combination (c j : ℤ) * h_ediv + (a : ℤ) * ht2
        have hz_ge1 : 1 ≤ z j := by
          by_contra h_not
          have hz0 : z j = 0 := by omega
          have h_rel0 : (p : ℤ) ∣ - ((a * D_q' : ℕ) : ℤ) := by
            convert h_rel using 1
            rw [hz0]
            push_cast
            ring
          have h_dvd_nat : p ∣ a * D_q' := Int.ofNat_dvd.mp (dvd_neg.mp h_rel0)
          have h_dvd_a : p ∣ a := h_cop_Dq'.dvd_of_dvd_mul_right h_dvd_nat
          have hp_le_a : p ≤ a := Nat.le_of_dvd (by omega) h_dvd_a
          omega
        exact ⟨hz_ge1, hz_lt_p, h_rel⟩
      let P : ℕ → Prop := fun j => B + 1 ≤ z j ∧ z j + (B + 1) ≤ p
      let U_good := U.filter P
      let U_bad := U.filter (fun j => ¬ P j)
      have h_part : U_good.card + U_bad.card = U.card :=
        Finset.card_filter_add_card_filter_not P
      let Z_bad : Finset ℕ := Finset.Ioc 0 B ∪ Finset.Ico (p - B) p
      have hZ_card : Z_bad.card ≤ 2 * B := by
        calc Z_bad.card ≤ (Finset.Ioc 0 B).card + (Finset.Ico (p - B) p).card := Finset.card_union_le _ _
          _ = B + (p - (p - B)) := by rw [Nat.card_Ioc, Nat.card_Ico, Nat.sub_zero]
          _ ≤ 2 * B := by omega
      let Φ : ℕ → ℕ × ℕ := fun j => (z j, c j / p)
      have h_maps : ∀ j ∈ U_bad, Φ j ∈ Z_bad ×ˢ Finset.range (q / p) := by
        intro j hj_bad
        have hj_U : j ∈ U := (Finset.mem_filter.mp hj_bad).1
        have hj_not_P : ¬ P j := (Finset.mem_filter.mp hj_bad).2
        have hj_lt_m : j < m := Finset.mem_range.mp (hU_sub_m hj_U)
        obtain ⟨hz1, hzp, _⟩ := hz_props j hj_lt_m
        have hz_in : z j ∈ Z_bad := by
          rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ico]
          dsimp [P] at hj_not_P
          omega
        have hc_lt : c j < q / 4 := (hc_props_m j hj_lt_m).1
        have hc_lt_q : c j < p * (q / p) := by
          have hq_pos : 0 < q := by
            rw [hq_eq]
            exact pow_pos hp_pos e
          omega
        have hdiv_lt : c j / p < q / p := Nat.div_lt_of_lt_mul (by linarith)
        exact Finset.mem_product.mpr ⟨hz_in, Finset.mem_range.mpr hdiv_lt⟩
      have h_inj : Set.InjOn Φ U_bad := by
        intro j₁ hj₁ j₂ hj₂ h_eq
        have hj₁_lt_m : j₁ < m := Finset.mem_range.mp (hU_sub_m (Finset.mem_filter.mp hj₁).1)
        have hj₂_lt_m : j₂ < m := Finset.mem_range.mp (hU_sub_m (Finset.mem_filter.mp hj₂).1)
        have hz_eq : z j₁ = z j₂ := (Prod.ext_iff.mp h_eq).1
        have hdiv_eq : c j₁ / p = c j₂ / p := (Prod.ext_iff.mp h_eq).2
        obtain ⟨hz1, hzp, h_rel1⟩ := hz_props j₁ hj₁_lt_m
        obtain ⟨_, _, h_rel2⟩ := hz_props j₂ hj₂_lt_m
        rw [← hz_eq] at h_rel2
        have h_sub_dvd : (p : ℤ) ∣ ((c j₁ : ℤ) - (c j₂ : ℤ)) * (z j₁ : ℤ) := by
          have h := dvd_sub h_rel1 h_rel2
          convert h using 1
          ring
        have h_nat_dvd : p ∣ ((c j₁ : ℤ) - (c j₂ : ℤ)).natAbs * z j₁ := by
          have h1 := Int.natAbs_dvd_natAbs.mpr h_sub_dvd
          rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h1
        have h_cop_z : Nat.Coprime p (z j₁) := by
          rw [hp.coprime_iff_not_dvd]
          intro hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        have h_dvd_diff : p ∣ ((c j₁ : ℤ) - (c j₂ : ℤ)).natAbs :=
          h_cop_z.dvd_of_dvd_mul_right h_nat_dvd
        have h_div1 := Nat.div_add_mod (c j₁) p
        have h_div2 := Nat.div_add_mod (c j₂) p
        have h_mod1 := Nat.mod_lt (c j₁) hp_pos
        have h_mod2 := Nat.mod_lt (c j₂) hp_pos
        have h_mul_div_eq : p * (c j₁ / p) = p * (c j₂ / p) := by rw [hdiv_eq]
        have h_diff_lt : ((c j₁ : ℤ) - (c j₂ : ℤ)).natAbs < p := by omega
        have h_diff_zero : ((c j₁ : ℤ) - (c j₂ : ℤ)).natAbs = 0 := by
          by_contra hne0
          have := Nat.le_of_dvd (by omega) h_dvd_diff
          omega
        have hc_eq : c j₁ = c j₂ := by omega
        by_contra hj_ne
        exact hc_inj_m j₁ hj₁_lt_m j₂ hj₂_lt_m hj_ne hc_eq
      have h_bad_le_prod : U_bad.card ≤ (Z_bad ×ˢ Finset.range (q / p)).card :=
        Finset.card_le_card_of_injOn Φ h_maps h_inj
      rw [Finset.card_product, Finset.card_range] at h_bad_le_prod
      have h_bad_le_2B : U_bad.card ≤ 2 * (B * (q / p)) := by
        calc U_bad.card ≤ Z_bad.card * (q / p) := h_bad_le_prod
          _ ≤ (2 * B) * (q / p) := Nat.mul_le_mul_right (q / p) hZ_card
          _ = 2 * (B * (q / p)) := by ring
      have h_bad_le_U8 : U_bad.card ≤ U.card / 8 := le_trans h_bad_le_2B h_2B_le
      change 7 * U.card / 8 ≤ U_good.card
      omega
    apply h_core (q / (512 * (Nat.log 2 q + 1))) (p / (2 ^ 25 * (Nat.log 2 q + 1))) hc_props_W hc_inj hU_sub
    set K : ℕ := Nat.log 2 q + 1
    set M : ℕ := 2 ^ 25 * K
    have hp_dvd_q : p ∣ q := by
      rw [hq_eq]
      exact dvd_pow_self p (by omega : e ≠ 0)
    have h_p_mul_qp : p * (q / p) = q := Nat.mul_div_cancel' hp_dvd_q
    have hM_pos : 0 < M := by positivity
    have hB_qp_le : (p / M) * (q / p) ≤ q / M := by
      rw [Nat.le_div_iff_mul_le hM_pos]
      calc (p / M) * (q / p) * M = (M * (p / M)) * (q / p) := by ring
        _ ≤ p * (q / p) := Nat.mul_le_mul_right (q / p) (Nat.mul_div_le p M)
        _ = q := h_p_mul_qp
    have h_div_chain : q / M = ((q / (512 * K)) / 2048) / 8 / 4 := by
      have hM_split : M = 512 * K * 2048 * 8 * 4 := by dsimp [M]; ring
      rw [hM_split, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have h_X_le_U8 : ((q / (512 * K)) / 2048) / 8 ≤ U.card / 8 :=
      Nat.div_le_div_right hU_card
    have h_two_div4 : ∀ n : ℕ, 2 * (n / 4) ≤ n := fun n => by omega
    calc 2 * ((p / M) * (q / p))
        ≤ 2 * (q / M) := Nat.mul_le_mul_left 2 hB_qp_le
      _ = 2 * (((q / (512 * K)) / 2048) / 8 / 4) := by rw [h_div_chain]
      _ ≤ ((q / (512 * K)) / 2048) / 8 := h_two_div4 _
      _ ≤ U.card / 8 := h_X_le_U8

  let Δ_q : Finset ℤ := (Finset.Ico 1 p).image (fun a : ℕ => (a : ℤ) * (L_q1 : ℤ))
  have hp_le_q : p ≤ q := by
    rw [hq_eq]
    simpa using Nat.pow_le_pow_right hp.pos he
  have hΔ_card : Δ_q.card ≤ q := by
    calc Δ_q.card ≤ (Finset.Ico 1 p).card := Finset.card_image_le
      _ = p - 1 := Nat.card_Ico 1 p
      _ ≤ p := Nat.sub_le p 1
      _ ≤ q := hp_le_q
  refine ⟨Δ_q, hΔ_card, ?_, ?_⟩
  · intro δ h_dvd h_not_dvd
    have h_not_dvd' : ¬ (((p * L_q1 : ℕ) : ℤ) ∣ δ) := by
      rwa [← hL_step]
    obtain ⟨a, ha_mem, ha_eq⟩ := h_s1.2 δ h_dvd h_not_dvd'
    refine ⟨(a : ℤ) * (L_q1 : ℤ), Finset.mem_image_of_mem _ ha_mem, fun j hj => ?_⟩
    have h_den : (((D_q : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).den = 1 := (hc_props j hj).2.2.1
    simpa [mul_assoc] using ha_eq (w_Icc (I j).1 (I j).2) h_den
  · intro δ₀ hδ₀ U hU_sub hU_card
    obtain ⟨a, ha_mem, rfl⟩ := Finset.mem_image.mp hδ₀
    have ha_low : 1 ≤ a := (Finset.mem_Ico.mp ha_mem).1
    have ha_high : a < p := (Finset.mem_Ico.mp ha_mem).2
    let W : ℕ → ℤ := fun j => (((D_q : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).num
    have h_good := h_s3 (D_q / q) a h_cop_Dq ha_low ha_high W
      (fun j hj => ⟨(hc_props j hj).1, (hc_props j hj).2.2.2⟩)
      U hU_sub hU_card
    refine le_trans h_good (Finset.card_le_card ?_)
    intro j hj
    have hj_U : j ∈ U := (Finset.mem_filter.mp hj).1
    have hj_P := (Finset.mem_filter.mp hj).2
    have hj_lt_m : j < q / (512 * (Nat.log 2 q + 1)) := Finset.mem_range.mp (hU_sub hj_U)
    have h_den : (((D_q : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).den = 1 := (hc_props j hj_lt_m).2.2.1
    have h_sin_red := h_s1.1 (w_Icc (I j).1 (I j).2) (a : ℤ) h_den
    have h_chord := h_s2 ((((a : ℤ) * W j) % (p : ℤ)).toNat) hj_P.1 hj_P.2
    rw [Finset.mem_filter]
    refine ⟨hj_U, ?_⟩
    have h_assoc : Real.pi * (((a : ℤ) * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ)) =
        Real.pi * ((((a : ℤ) * (L_q1 : ℤ) : ℤ) : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ))) := by
      ring
    rw [h_assoc, h_sin_red]
    exact h_chord

theorem prime_power_digit_reservoir_existence : ∃ (B : ℕ) (m_res : ℕ → ℕ) (I_res : ℕ → ℕ → ℕ × ℕ),
      2 ^ 128 ≤ B ∧
      (∀ q > B, ∀ j < m_res q,
        q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ (I_res q j).1 ∧
        (I_res q j).2 = (I_res q j).1 + 1 ∧
        (I_res q j).2 ≤ q ^ 2 / 2 ∧
        w_Icc (I_res q j).1 (I_res q j).2 ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2) ∧
      (∀ q > B, ∀ j₁ < m_res q, ∀ j₂ < m_res q, j₁ ≠ j₂ →
        (I_res q j₁).2 + 1 < (I_res q j₂).1 ∨ (I_res q j₂).2 + 1 < (I_res q j₁).1) ∧
      (∀ q₁ > B, ∀ q₂ > B, ∀ j₁ < m_res q₁, ∀ j₂ < m_res q₂,
        (q₁ ≠ q₂ ∨ j₁ ≠ j₂) → (I_res q₁ j₁).1 ≠ (I_res q₂ j₂).1) ∧
      (∀ q > B, ∀ j < m_res q,
        ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I_res q j).1 (I_res q j).2).den = 1) ∧
      (∀ q > B,
        (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189 → m_res q = 0) ∧
        (¬ (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189) →
          m_res q = q / (512 * (Nat.log 2 q + 1)) ∧
          ∃ Δ_q : Finset ℤ, Δ_q.card ≤ q ∧
            (∀ δ : ℤ,
              ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
              ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
              ∃ δ₀ ∈ Δ_q, ∀ j < m_res q,
                (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 =
                (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) ∧
            (∀ δ₀ ∈ Δ_q, ∀ U ⊆ Finset.range (m_res q), m_res q / 2048 ≤ U.card →
              7 * U.card / 8 ≤
                (U.filter (fun j =>
                  (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
                    (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2)).card))) :=
by
  classical
  have h_s1 := lcm_jump_prime_power_structure
  let B : ℕ := 2 ^ 128
  let IsJump : ℕ → Prop := fun q =>
    B < q ∧ ¬ (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189)
  let m_res : ℕ → ℕ := fun q =>
    if IsJump q then q / (512 * (Nat.log 2 q + 1)) else 0
  have h_q_all : ∀ q : ℕ, ∃ (I : ℕ → ℕ × ℕ),
      IsJump q →
        (∀ j < q / (512 * (Nat.log 2 q + 1)),
          q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ (I j).1 ∧
          (I j).2 = (I j).1 + 1 ∧
          (I j).2 ≤ q ^ 2 / 2 ∧
          w_Icc (I j).1 (I j).2 ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2 ∧
          q ∣ (I j).1 * ((I j).1 + 1) ∧
          ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I j).1 (I j).2).den = 1) ∧
        (∀ j₁ < q / (512 * (Nat.log 2 q + 1)), ∀ j₂ < q / (512 * (Nat.log 2 q + 1)), j₁ ≠ j₂ →
          ((I j₁).2 + 1 < (I j₂).1 ∨ (I j₂).2 + 1 < (I j₁).1)) ∧
        (∃ Δ_q : Finset ℤ, Δ_q.card ≤ q ∧
          (∀ δ : ℤ,
            ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
            ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
            ∃ δ₀ ∈ Δ_q, ∀ j < q / (512 * (Nat.log 2 q + 1)),
              (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ)))) ^ 2 =
              (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ)))) ^ 2) ∧
          (∀ δ₀ ∈ Δ_q, ∀ U ⊆ Finset.range (q / (512 * (Nat.log 2 q + 1))),
            (q / (512 * (Nat.log 2 q + 1))) / 2048 ≤ U.card →
            7 * U.card / 8 ≤
              (U.filter (fun j =>
                (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
                  (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I j).1 (I j).2 : ℝ)))) ^ 2)).card)) := by
    intro q
    by_cases hJ : IsJump q
    · obtain ⟨p, e, hp, he, hq_eq, hD_step, hL_step, hL_prev, hL_curr, h_cop_Dq⟩ :=
        h_s1.1 q hJ.1 hJ.2
      obtain ⟨I, c, hc_all, hc_pair⟩ :=
        single_prime_power_cofactor_reservoir_construction q p e hJ.1 hp he hq_eq
      have h_phase := inverse_residue_phase_distribution_bound q p e hJ.1 hp he hq_eq
        hD_step hL_step hL_prev hL_curr h_cop_Dq I c
        (fun j hj => ⟨(hc_all j hj).2.1, (hc_all j hj).2.2.1,
          (hc_all j hj).2.2.2.2.2.2.2.2.1, (hc_all j hj).2.2.2.2.2.2.2.2.2⟩)
        (fun j₁ hj₁ j₂ hj₂ hne => (hc_pair j₁ hj₁ j₂ hj₂ hne).1)
      refine ⟨I, fun _ => ⟨?_, ?_, h_phase⟩⟩
      · intro j hj
        have h := hc_all j hj
        exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩
      · intro j₁ hj₁ j₂ hj₂ hne
        exact (hc_pair j₁ hj₁ j₂ hj₂ hne).2
    · exact ⟨fun _ => (0, 0), fun h => False.elim (hJ h)⟩
  let I_res : ℕ → ℕ → ℕ × ℕ := fun q => Classical.choose (h_q_all q)
  have hI_res : ∀ q : ℕ, IsJump q →
      (∀ j < q / (512 * (Nat.log 2 q + 1)),
        q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ (I_res q j).1 ∧
        (I_res q j).2 = (I_res q j).1 + 1 ∧
        (I_res q j).2 ≤ q ^ 2 / 2 ∧
        w_Icc (I_res q j).1 (I_res q j).2 ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2 ∧
        q ∣ (I_res q j).1 * ((I_res q j).1 + 1) ∧
        ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I_res q j).1 (I_res q j).2).den = 1) ∧
      (∀ j₁ < q / (512 * (Nat.log 2 q + 1)), ∀ j₂ < q / (512 * (Nat.log 2 q + 1)), j₁ ≠ j₂ →
        ((I_res q j₁).2 + 1 < (I_res q j₂).1 ∨ (I_res q j₂).2 + 1 < (I_res q j₁).1)) ∧
      (∃ Δ_q : Finset ℤ, Δ_q.card ≤ q ∧
        (∀ δ : ℤ,
          ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
          ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
          ∃ δ₀ ∈ Δ_q, ∀ j < q / (512 * (Nat.log 2 q + 1)),
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 =
            (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) ∧
        (∀ δ₀ ∈ Δ_q, ∀ U ⊆ Finset.range (q / (512 * (Nat.log 2 q + 1))),
          (q / (512 * (Nat.log 2 q + 1))) / 2048 ≤ U.card →
          7 * U.card / 8 ≤
            (U.filter (fun j =>
              (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
                (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2)).card)) :=
    fun q => Classical.choose_spec (h_q_all q)
  have h_jump_of_lt : ∀ q j : ℕ, j < m_res q → IsJump q ∧ j < q / (512 * (Nat.log 2 q + 1)) := by
    intro q j hj
    dsimp [m_res] at hj
    split_ifs at hj with hJ
    · exact ⟨hJ, hj⟩
    · omega
  have h_a_pos : ∀ q j : ℕ, j < m_res q → 1 ≤ (I_res q j).1 := by
    intro q j hj
    obtain ⟨hJ, hj'⟩ := h_jump_of_lt q j hj
    have h_low := ((hI_res q hJ).1 j hj').1
    have hq_gt : 2 ^ 128 < q := hJ.1
    have h_log : Nat.log 2 q < q := Nat.log_lt_self 2 (by omega)
    have h_mul : 2048 * (Nat.log 2 q + 1) ≤ q ^ 2 := by nlinarith
    have h_div : 1 ≤ q ^ 2 / (2048 * (Nat.log 2 q + 1)) := Nat.div_pos h_mul (by omega)
    exact le_trans h_div h_low
  refine ⟨B, m_res, I_res, le_refl B, ?_, ?_, ?_, ?_, ?_⟩
  · intro q _ j hj
    obtain ⟨hJ, hj'⟩ := h_jump_of_lt q j hj
    obtain ⟨h1, h2, h3, h4, _, _⟩ := (hI_res q hJ).1 j hj'
    exact ⟨h1, h2, h3, h4⟩
  · intro q _ j₁ hj₁ j₂ hj₂ hne
    obtain ⟨hJ, hj₁'⟩ := h_jump_of_lt q j₁ hj₁
    obtain ⟨_, hj₂'⟩ := h_jump_of_lt q j₂ hj₂
    exact (hI_res q hJ).2.1 j₁ hj₁' j₂ hj₂' hne
  · intro q₁ _ q₂ _ j₁ hj₁ j₂ hj₂ h_or
    obtain ⟨hJ₁, hj₁'⟩ := h_jump_of_lt q₁ j₁ hj₁
    obtain ⟨hJ₂, hj₂'⟩ := h_jump_of_lt q₂ j₂ hj₂
    rcases lt_trichotomy q₁ q₂ with hlt | rfl | hgt
    · have ha₁ : 1 ≤ (I_res q₁ j₁).1 := h_a_pos q₁ j₁ hj₁
      obtain ⟨_, h2₁, _, _, _, h_den₁⟩ := (hI_res q₁ hJ₁).1 j₁ hj₁'
      obtain ⟨_, _, _, _, h_dvd₂, _⟩ := (hI_res q₂ hJ₂).1 j₂ hj₂'
      rw [h2₁] at h_den₁
      exact h_s1.2 q₁ q₂ (I_res q₁ j₁).1 (I_res q₂ j₂).1 hJ₁.1 hlt hJ₂.2 ha₁ h_den₁ h_dvd₂
    · have hj_ne : j₁ ≠ j₂ := h_or.resolve_left (fun h => h rfl)
      have h2₁ : (I_res q₁ j₁).2 = (I_res q₁ j₁).1 + 1 := ((hI_res q₁ hJ₁).1 j₁ hj₁').2.1
      have h2₂ : (I_res q₁ j₂).2 = (I_res q₁ j₂).1 + 1 := ((hI_res q₁ hJ₁).1 j₂ hj₂').2.1
      have h_sep := (hI_res q₁ hJ₁).2.1 j₁ hj₁' j₂ hj₂' hj_ne
      omega
    · have ha₂ : 1 ≤ (I_res q₂ j₂).1 := h_a_pos q₂ j₂ hj₂
      obtain ⟨_, h2₂, _, _, _, h_den₂⟩ := (hI_res q₂ hJ₂).1 j₂ hj₂'
      obtain ⟨_, _, _, _, h_dvd₁, _⟩ := (hI_res q₁ hJ₁).1 j₁ hj₁'
      rw [h2₂] at h_den₂
      exact Ne.symm (h_s1.2 q₂ q₁ (I_res q₂ j₂).1 (I_res q₁ j₁).1 hJ₂.1 hgt hJ₁.2 ha₂ h_den₂ h_dvd₁)
  · intro q _ j hj
    obtain ⟨hJ, hj'⟩ := h_jump_of_lt q j hj
    exact ((hI_res q hJ).1 j hj').2.2.2.2.2
  · intro q hq
    constructor
    · intro h_dvd
      dsimp [m_res, IsJump]
      exact if_neg (fun hJ => hJ.2 h_dvd)
    · intro h_not_dvd
      have hJ : IsJump q := ⟨hq, h_not_dvd⟩
      have hm_eq : m_res q = q / (512 * (Nat.log 2 q + 1)) := if_pos hJ
      refine ⟨hm_eq, ?_⟩
      rw [hm_eq]
      exact (hI_res q hJ).2.2

theorem bounded_degree_simultaneous_independent_thinning (Q : Finset ℕ) (C : ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ)
    (h_cap : ∀ q ∈ Q, 2 ^ 37 ≤ (C q).card)
    (h_inj : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ j₁ ∈ C q₁, ∀ j₂ ∈ C q₂,
      (q₁ ≠ q₂ ∨ j₁ ≠ j₂) → a q₁ j₁ ≠ a q₂ j₂)
    (h_sep : ∀ q ∈ Q, ∀ j₁ ∈ C q, ∀ j₂ ∈ C q, j₁ ≠ j₂ →
      a q j₁ + 5 < a q j₂ ∨ a q j₂ + 5 < a q j₁) :
    ∃ U_M : ℕ → Finset ℕ,
      (∀ q ∈ Q, U_M q ⊆ C q ∧ (C q).card / 1024 ≤ (U_M q).card) ∧
      (∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ j₁ ∈ U_M q₁, ∀ j₂ ∈ U_M q₂,
        (q₁ ≠ q₂ ∨ j₁ ≠ j₂) →
        a q₁ j₁ + 2 < a q₂ j₂ ∨ a q₂ j₂ + 2 < a q₁ j₁) :=
by
  classical
  
  let A : Finset ℕ := Q.biUnion (fun q => (C q).image (a q))
  let N_A : ℕ → Finset ℕ := fun x => A ∩ Finset.Icc (x - 2) (x + 2)
  let W : ℕ → Finset ℕ := fun q => (C q).biUnion (fun j => N_A (a q j))
  let U : Finset ℕ → ℕ → Finset ℕ := fun S q => (C q).filter (fun j => S ∩ N_A (a q j) = {a q j})
  let Γ : ℕ → Finset ℕ := fun q => (Q \ {q}).filter (fun q' => ¬ Disjoint (W q) (W q'))

  have hN_card : ∀ x : ℕ, (N_A x).card ≤ 5 := by
    intro x
    calc (N_A x).card ≤ (Finset.Icc (x - 2) (x + 2)).card :=
          Finset.card_le_card Finset.inter_subset_right
      _ = x + 2 + 1 - (x - 2) := Nat.card_Icc (x - 2) (x + 2)
      _ ≤ 5 := by omega

  have h_mem_A : ∀ q ∈ Q, ∀ j ∈ C q, a q j ∈ A := by
    intro q hq j hj
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image_of_mem _ hj⟩

  have h_mem_N_self : ∀ q ∈ Q, ∀ j ∈ C q, a q j ∈ N_A (a q j) := by
    intro q hq j hj
    exact Finset.mem_inter.mpr ⟨h_mem_A q hq j hj, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

  have h_geom : ∀ q ∈ Q, ∀ j ∈ C q,
      a q j ∈ N_A (a q j) ∧ N_A (a q j) ⊆ W q ∧ W q ⊆ A ∧ (N_A (a q j)).card ≤ 5 := by
    intro q hq j hj
    refine ⟨h_mem_N_self q hq j hj, ?_, ?_, hN_card (a q j)⟩
    · exact Finset.subset_biUnion_of_mem (fun k => N_A (a q k)) hj
    · exact Finset.biUnion_subset.mpr (fun k _ => Finset.inter_subset_left)

  have h_disj_N : ∀ q ∈ Q, ∀ j₁ ∈ C q, ∀ j₂ ∈ C q, j₁ ≠ j₂ →
      Disjoint (N_A (a q j₁)) (N_A (a q j₂)) := by
    intro q hq j₁ hj₁ j₂ hj₂ hne
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    have h₁ := Finset.mem_Icc.mp (Finset.mem_inter.mp hy₁).2
    have h₂ := Finset.mem_Icc.mp (Finset.mem_inter.mp hy₂).2
    have hs := h_sep q hq j₁ hj₁ j₂ hj₂ hne
    omega

  have h_det_sep : ∀ (S : Finset ℕ), ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ j₁ ∈ U S q₁, ∀ j₂ ∈ U S q₂,
      (q₁ ≠ q₂ ∨ j₁ ≠ j₂) → a q₁ j₁ + 2 < a q₂ j₂ ∨ a q₂ j₂ + 2 < a q₁ j₁ := by
    intro S q₁ hq₁ q₂ hq₂ j₁ hj₁ j₂ hj₂ hne
    by_contra h_not_sep
    have hj₁_f := Finset.mem_filter.mp hj₁
    have hj₂_f := Finset.mem_filter.mp hj₂
    have ha₂_in_inter : a q₂ j₂ ∈ S ∩ N_A (a q₂ j₂) := by
      rw [hj₂_f.2]
      exact Finset.mem_singleton_self _
    have ha₂_in_S : a q₂ j₂ ∈ S := (Finset.mem_inter.mp ha₂_in_inter).1
    have ha₂_in_N₁ : a q₂ j₂ ∈ N_A (a q₁ j₁) := by
      refine Finset.mem_inter.mpr ⟨h_mem_A q₂ hq₂ j₂ hj₂_f.1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    have ha₂_in_inter₁ : a q₂ j₂ ∈ S ∩ N_A (a q₁ j₁) := Finset.mem_inter.mpr ⟨ha₂_in_S, ha₂_in_N₁⟩
    rw [hj₁_f.2, Finset.mem_singleton] at ha₂_in_inter₁
    exact h_inj q₁ hq₁ q₂ hq₂ j₁ hj₁_f.1 j₂ hj₂_f.1 hne ha₂_in_inter₁.symm

  have h_deg : ∀ q ∈ Q, (Γ q).card ≤ 25 * (C q).card := by
    intro q hq
    let W2 : Finset ℕ := (W q).biUnion N_A
    have hW_card : (W q).card ≤ (C q).card * 5 :=
      Finset.card_biUnion_le_card_mul (C q) (fun j => N_A (a q j)) 5 (fun j _ => hN_card (a q j))
    have hW2_card : W2.card ≤ (W q).card * 5 :=
      Finset.card_biUnion_le_card_mul (W q) N_A 5 (fun y _ => hN_card y)
    have hW2_le : W2.card ≤ 25 * (C q).card := by omega
    have h_ex_j : ∀ q' ∈ Γ q, ∃ j' ∈ C q', a q' j' ∈ W2 := by
      intro q' hq'
      have hq'_f := Finset.mem_filter.mp hq'
      have hq'_Q : q' ∈ Q := (Finset.mem_sdiff.mp hq'_f.1).1
      obtain ⟨y, hyW, hyW'⟩ := Finset.not_disjoint_iff.mp hq'_f.2
      obtain ⟨j', hj'C, hyN'⟩ := Finset.mem_biUnion.mp hyW'
      refine ⟨j', hj'C, Finset.mem_biUnion.mpr ⟨y, hyW, ?_⟩⟩
      have hy_Icc := Finset.mem_Icc.mp (Finset.mem_inter.mp hyN').2
      exact Finset.mem_inter.mpr ⟨h_mem_A q' hq'_Q j' hj'C, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    let φ : ℕ → ℕ := fun q' =>
      if h : q' ∈ Γ q then a q' (Classical.choose (h_ex_j q' h)) else 0
    have hφ_maps : ∀ q' ∈ Γ q, φ q' ∈ W2 := by
      intro q' hq'
      dsimp [φ]
      rw [dif_pos hq']
      exact (Classical.choose_spec (h_ex_j q' hq')).2
    have hφ_inj : Set.InjOn φ (Γ q) := by
      intro q₁ hq₁ q₂ hq₂ h_eq
      have hq₁' : q₁ ∈ Γ q := Finset.mem_coe.mp hq₁
      have hq₂' : q₂ ∈ Γ q := Finset.mem_coe.mp hq₂
      by_contra hne_q
      dsimp [φ] at h_eq
      rw [dif_pos hq₁', dif_pos hq₂'] at h_eq
      have hq₁_Q : q₁ ∈ Q := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq₁').1).1
      have hq₂_Q : q₂ ∈ Q := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq₂').1).1
      have hj₁_C := (Classical.choose_spec (h_ex_j q₁ hq₁')).1
      have hj₂_C := (Classical.choose_spec (h_ex_j q₂ hq₂')).1
      exact h_inj q₁ hq₁_Q q₂ hq₂_Q _ hj₁_C _ hj₂_C (Or.inl hne_q) h_eq
    exact le_trans (Finset.card_le_card_of_injOn φ hφ_maps hφ_inj) hW2_le

  
  have h_avg_step : ∀ (N₀ : Finset ℕ) (a₀ : ℕ),
      N₀ ⊆ A → a₀ ∈ N₀ → N₀.card ≤ 5 →
      ∀ (P : Finset ℕ → Prop) [DecidablePred P] (f : Finset ℕ → ℚ),
      (∀ S ⊆ A, 0 ≤ f S) →
      (∀ S ⊆ A, ∀ T ⊆ N₀, (P ((S \ N₀) ∪ T) ↔ P S) ∧ f ((S \ N₀) ∪ T) = f S) →
      ∑ S ∈ A.powerset.filter P, f S * (if S ∩ N₀ = {a₀} then (1 / 2 : ℚ) else 1) ≤
        (63 / 64 : ℚ) * ∑ S ∈ A.powerset.filter P, f S := by
    intro N₀ a₀ hN₀_sub ha₀_mem hN₀_card P _ f hf_nonneg h_inv
    let R := (A \ N₀).powerset.filter P
    let M := N₀.powerset
    have h_sdiff_self : ∀ S₁ ⊆ A \ N₀, S₁ \ N₀ = S₁ := by
      intro S₁ hS₁
      ext x
      simp only [Finset.mem_sdiff]
      exact ⟨fun h => h.1, fun hx => ⟨hx, (Finset.mem_sdiff.mp (hS₁ hx)).2⟩⟩
    have h_union_sdiff : ∀ S₁ ⊆ A \ N₀, ∀ T ⊆ N₀, (S₁ ∪ T) \ N₀ = S₁ := by
      intro S₁ hS₁ T hT
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxS₁ | hxT, hxN₀⟩
        · exact hxS₁
        · exact (hxN₀ (hT hxT)).elim
      · intro hxS₁
        exact ⟨Or.inl hxS₁, (Finset.mem_sdiff.mp (hS₁ hxS₁)).2⟩
    have h_union_inter : ∀ S₁ ⊆ A \ N₀, ∀ T ⊆ N₀, (S₁ ∪ T) ∩ N₀ = T := by
      intro S₁ hS₁ T hT
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxS₁ | hxT, hxN₀⟩
        · exact ((Finset.mem_sdiff.mp (hS₁ hxS₁)).2 hxN₀).elim
        · exact hxT
      · intro hxT
        exact ⟨Or.inr hxT, hT hxT⟩
    have h_sum_split : ∀ (g : Finset ℕ → ℚ),
        ∑ S ∈ A.powerset.filter P, g S = ∑ S₁ ∈ R, ∑ T ∈ M, g (S₁ ∪ T) := by
      intro g
      rw [← Finset.sum_product' R M (fun S₁ T => g (S₁ ∪ T))]
      refine (Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun S => (S \ N₀, S ∩ N₀)) ?_ ?_ ?_ ?_ ?_).symm
      · intro p hp
        rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
        have hS₁_f := Finset.mem_filter.mp hp₁
        have hS₁_sub : p.1 ⊆ A \ N₀ := Finset.mem_powerset.mp hS₁_f.1
        have hS₁_A : p.1 ⊆ A := Finset.Subset.trans hS₁_sub Finset.sdiff_subset
        have hT_sub : p.2 ⊆ N₀ := Finset.mem_powerset.mp hp₂
        have h_u_sub : p.1 ∪ p.2 ⊆ A := Finset.union_subset hS₁_A (Finset.Subset.trans hT_sub hN₀_sub)
        have h_P_eq : P ((p.1 \ N₀) ∪ p.2) ↔ P p.1 := (h_inv p.1 hS₁_A p.2 hT_sub).1
        rw [h_sdiff_self p.1 hS₁_sub] at h_P_eq
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h_u_sub, h_P_eq.mpr hS₁_f.2⟩
      · intro S hS
        have hS_f := Finset.mem_filter.mp hS
        have hS_A : S ⊆ A := Finset.mem_powerset.mp hS_f.1
        have h_sdiff_sub : S \ N₀ ⊆ A \ N₀ := Finset.sdiff_subset_sdiff hS_A (Finset.Subset.refl N₀)
        have h_P_empty := (h_inv S hS_A ∅ (Finset.empty_subset N₀)).1
        rw [Finset.union_empty] at h_P_empty
        refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h_sdiff_sub, h_P_empty.mpr hS_f.2⟩,
          Finset.mem_powerset.mpr Finset.inter_subset_right⟩
      · intro p hp
        rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
        have hS₁_sub : p.1 ⊆ A \ N₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hp₁).1
        have hT_sub : p.2 ⊆ N₀ := Finset.mem_powerset.mp hp₂
        exact Prod.ext (h_union_sdiff p.1 hS₁_sub p.2 hT_sub) (h_union_inter p.1 hS₁_sub p.2 hT_sub)
      · intro S _
        exact Finset.sdiff_union_inter S N₀
      · intro p _
        rfl
    rw [h_sum_split (fun S => f S * (if S ∩ N₀ = {a₀} then (1 / 2 : ℚ) else 1)),
        h_sum_split f, Finset.mul_sum]
    refine Finset.sum_le_sum (fun S₁ hS₁ => ?_)
    have hS₁_sub : S₁ ⊆ A \ N₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₁).1
    have hS₁_A : S₁ ⊆ A := Finset.Subset.trans hS₁_sub Finset.sdiff_subset
    have h_lhs_S₁ : ∑ T ∈ M, f (S₁ ∪ T) * (if (S₁ ∪ T) ∩ N₀ = {a₀} then (1 / 2 : ℚ) else 1) =
        f S₁ * ∑ T ∈ M, (if T = {a₀} then (1 / 2 : ℚ) else 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun T hT => ?_)
      have hT_sub : T ⊆ N₀ := Finset.mem_powerset.mp hT
      have hf_eq := (h_inv S₁ hS₁_A T hT_sub).2
      rw [h_sdiff_self S₁ hS₁_sub] at hf_eq
      rw [hf_eq, h_union_inter S₁ hS₁_sub T hT_sub]
    have h_rhs_S₁ : ∑ T ∈ M, f (S₁ ∪ T) = f S₁ * (M.card : ℚ) := by
      have h_congr : ∑ T ∈ M, f (S₁ ∪ T) = ∑ _T ∈ M, f S₁ := by
        refine Finset.sum_congr rfl (fun T hT => ?_)
        have hT_sub : T ⊆ N₀ := Finset.mem_powerset.mp hT
        have hf_eq := (h_inv S₁ hS₁_A T hT_sub).2
        rw [h_sdiff_self S₁ hS₁_sub] at hf_eq
        exact hf_eq
      rw [h_congr, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [h_lhs_S₁, h_rhs_S₁]
    have ha₀_M : {a₀} ∈ M := Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha₀_mem)
    have h_M_sum : ∑ T ∈ M, (if T = {a₀} then (1 / 2 : ℚ) else 1) = (M.card : ℚ) - 1 / 2 := by
      have h_split := Finset.add_sum_erase M (fun T => if T = {a₀} then (1 / 2 : ℚ) else 1) ha₀_M
      rw [← h_split]
      have h_erase : ∑ T ∈ M.erase {a₀}, (if T = {a₀} then (1 / 2 : ℚ) else 1) = ((M.erase {a₀}).card : ℚ) := by
        have h_c : ∑ T ∈ M.erase {a₀}, (if T = {a₀} then (1 / 2 : ℚ) else 1) = ∑ _T ∈ M.erase {a₀}, (1 : ℚ) := by
          refine Finset.sum_congr rfl (fun T hT => ?_)
          rw [if_neg (Finset.ne_of_mem_erase hT)]
        rw [h_c, Finset.sum_const, nsmul_eq_mul, mul_one]
      dsimp only
      rw [if_pos rfl, h_erase, Finset.card_erase_of_mem ha₀_M]
      have hM_pos : 1 ≤ M.card := Finset.card_pos.mpr ⟨{a₀}, ha₀_M⟩
      rw [Nat.cast_sub hM_pos, Nat.cast_one]
      ring
    rw [h_M_sum]
    have hM_card_le : M.card ≤ 32 := by
      dsimp [M]
      rw [Finset.card_powerset]
      calc 2 ^ N₀.card ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hN₀_card
        _ = 32 := by decide
    have hM_q_le : (M.card : ℚ) ≤ 32 := by exact_mod_cast hM_card_le
    have h_avg_ineq : (M.card : ℚ) - 1 / 2 ≤ (63 / 64 : ℚ) * (M.card : ℚ) := by linarith
    have hf_pos : 0 ≤ f S₁ := hf_nonneg S₁ hS₁_A
    have h_mul := mul_le_mul_of_nonneg_left h_avg_ineq hf_pos
    linarith

  
  have h_cond_bound : ∀ q ∈ Q, ∀ (P : Finset ℕ → Prop) [DecidablePred P],
      (∀ j ∈ C q, ∀ S ⊆ A, ∀ T ⊆ N_A (a q j), P ((S \ N_A (a q j)) ∪ T) ↔ P S) →
      ((A.powerset.filter (fun S => (U S q).card < (C q).card / 1024 ∧ P S)).card : ℚ) ≤
        (1 / 4 : ℚ) ^ ((C q).card / 1024) * ((A.powerset.filter P).card : ℚ) := by
    intro q hq P _ hP_inv
    let U_sub : Finset ℕ → Finset ℕ → Finset ℕ := fun C' S =>
      C'.filter (fun j => S ∩ N_A (a q j) = {a q j})
    have h_moment : ∀ C' ⊆ C q,
        ∑ S ∈ A.powerset.filter P, (1 / 2 : ℚ) ^ (U_sub C' S).card ≤
          (63 / 64 : ℚ) ^ C'.card * ((A.powerset.filter P).card : ℚ) := by
      intro C'
      induction' C' using Finset.induction_on with j₀ C'' hj₀ ih
      · intro _
        have h_U0 : ∀ S : Finset ℕ, (U_sub ∅ S).card = 0 := fun _ => rfl
        simp [h_U0]
      · intro h_sub
        have hj₀_C : j₀ ∈ C q := h_sub (Finset.mem_insert_self j₀ C'')
        have hC''_C : C'' ⊆ C q := Finset.Subset.trans (Finset.subset_insert j₀ C'') h_sub
        have h_ih := ih hC''_C
        have h_step_term : ∀ S : Finset ℕ,
            (1 / 2 : ℚ) ^ (U_sub (insert j₀ C'') S).card =
              (1 / 2 : ℚ) ^ (U_sub C'' S).card * (if S ∩ N_A (a q j₀) = {a q j₀} then (1 / 2 : ℚ) else 1) := by
          intro S
          dsimp [U_sub]
          rw [Finset.filter_insert]
          split_ifs with h_hit
          · have hj₀_not : j₀ ∉ C''.filter (fun j => S ∩ N_A (a q j) = {a q j}) :=
              fun h_in => hj₀ (Finset.mem_of_mem_filter j₀ h_in)
            rw [Finset.card_insert_of_notMem hj₀_not, pow_succ]
          · rw [mul_one]
        have h_sum_eq : ∑ S ∈ A.powerset.filter P, (1 / 2 : ℚ) ^ (U_sub (insert j₀ C'') S).card =
            ∑ S ∈ A.powerset.filter P,
              (1 / 2 : ℚ) ^ (U_sub C'' S).card * (if S ∩ N_A (a q j₀) = {a q j₀} then (1 / 2 : ℚ) else 1) :=
          Finset.sum_congr rfl (fun S _ => h_step_term S)
        rw [h_sum_eq]
        have hf_inv : ∀ S ⊆ A, ∀ T ⊆ N_A (a q j₀),
            (P ((S \ N_A (a q j₀)) ∪ T) ↔ P S) ∧
              (1 / 2 : ℚ) ^ (U_sub C'' ((S \ N_A (a q j₀)) ∪ T)).card = (1 / 2 : ℚ) ^ (U_sub C'' S).card := by
          intro S hSA T hTN₀
          refine ⟨hP_inv j₀ hj₀_C S hSA T hTN₀, ?_⟩
          have h_U_eq : U_sub C'' ((S \ N_A (a q j₀)) ∪ T) = U_sub C'' S := by
            dsimp [U_sub]
            refine Finset.filter_congr (fun j hj => ?_)
            have hne : j₀ ≠ j := fun h_eq => hj₀ (h_eq ▸ hj)
            have h_disj : Disjoint (N_A (a q j₀)) (N_A (a q j)) :=
              h_disj_N q hq j₀ hj₀_C j (hC''_C hj) hne
            have h_inter_eq : ((S \ N_A (a q j₀)) ∪ T) ∩ N_A (a q j) = S ∩ N_A (a q j) := by
              ext x
              simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
              constructor
              · rintro ⟨⟨hxS, _⟩ | hxT, hxNj⟩
                · exact ⟨hxS, hxNj⟩
                · exact (Finset.disjoint_left.mp h_disj (hTN₀ hxT) hxNj).elim
              · rintro ⟨hxS, hxNj⟩
                exact ⟨Or.inl ⟨hxS, fun hxNj₀ => Finset.disjoint_left.mp h_disj hxNj₀ hxNj⟩, hxNj⟩
            rw [h_inter_eq]
          rw [h_U_eq]
        have h_geom_j₀ := h_geom q hq j₀ hj₀_C
        have h_avg := h_avg_step (N_A (a q j₀)) (a q j₀)
          (Finset.Subset.trans h_geom_j₀.2.1 h_geom_j₀.2.2.1) h_geom_j₀.1 h_geom_j₀.2.2.2 P
          (fun S => (1 / 2 : ℚ) ^ (U_sub C'' S).card)
          (fun S _ => by positivity) hf_inv
        have h_mul := mul_le_mul_of_nonneg_left h_ih (by norm_num : (0 : ℚ) ≤ 63 / 64)
        rw [← mul_assoc, ← pow_succ', ← Finset.card_insert_of_notMem hj₀] at h_mul
        exact le_trans h_avg h_mul
    let K := (C q).card / 1024
    let E_P := A.powerset.filter (fun S => (U S q).card < K ∧ P S)
    have h_EP_sub : E_P ⊆ A.powerset.filter P := by
      intro S hS
      simp only [E_P, Finset.mem_filter] at hS ⊢
      exact ⟨hS.1, hS.2.2⟩
    have h_term_ge : ∀ S ∈ E_P, (1 / 2 : ℚ) ^ K ≤ (1 / 2 : ℚ) ^ (U_sub (C q) S).card := by
      intro S hS
      have h_lt : (U S q).card < K := (Finset.mem_filter.mp hS).2.1
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_lt h_lt)
    have h_markov1 := Finset.card_nsmul_le_sum E_P (fun S => (1 / 2 : ℚ) ^ (U_sub (C q) S).card) ((1 / 2 : ℚ) ^ K) h_term_ge
    rw [nsmul_eq_mul] at h_markov1
    have h_markov2 : ∑ S ∈ E_P, (1 / 2 : ℚ) ^ (U_sub (C q) S).card ≤
        ∑ S ∈ A.powerset.filter P, (1 / 2 : ℚ) ^ (U_sub (C q) S).card :=
      Finset.sum_le_sum_of_subset_of_nonneg h_EP_sub (fun _ _ _ => by positivity)
    have h_markov3 := le_trans h_markov1 (le_trans h_markov2 (h_moment (C q) (Finset.Subset.refl (C q))))
    have h_256K : 256 * K ≤ (C q).card := by
      have := Nat.mul_div_le (C q).card 1024
      omega
    have h_pow_63 : (63 / 64 : ℚ) ^ (C q).card ≤ ((63 / 64 : ℚ) ^ 256) ^ K := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h_256K
    have h_markov4 : (E_P.card : ℚ) * (1 / 2 : ℚ) ^ K ≤
        ((63 / 64 : ℚ) ^ 256) ^ K * ((A.powerset.filter P).card : ℚ) :=
      le_trans h_markov3 (mul_le_mul_of_nonneg_right h_pow_63 (Nat.cast_nonneg _))
    have h_mul_2K := mul_le_mul_of_nonneg_left h_markov4 (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ K)
    have h_lhs_cancel : (2 : ℚ) ^ K * ((E_P.card : ℚ) * (1 / 2 : ℚ) ^ K) = (E_P.card : ℚ) := by
      calc (2 : ℚ) ^ K * ((E_P.card : ℚ) * (1 / 2 : ℚ) ^ K)
          = (E_P.card : ℚ) * ((2 : ℚ) ^ K * (1 / 2 : ℚ) ^ K) := by ring
        _ = (E_P.card : ℚ) * ((2 * (1 / 2) : ℚ) ^ K) := by rw [← mul_pow]
        _ = (E_P.card : ℚ) := by norm_num
    have h_rhs_combine : (2 : ℚ) ^ K * (((63 / 64 : ℚ) ^ 256) ^ K * ((A.powerset.filter P).card : ℚ)) =
        (2 * (63 / 64 : ℚ) ^ 256) ^ K * ((A.powerset.filter P).card : ℚ) := by
      calc (2 : ℚ) ^ K * (((63 / 64 : ℚ) ^ 256) ^ K * ((A.powerset.filter P).card : ℚ))
          = ((2 : ℚ) ^ K * ((63 / 64 : ℚ) ^ 256) ^ K) * ((A.powerset.filter P).card : ℚ) := by ring
        _ = (2 * (63 / 64 : ℚ) ^ 256) ^ K * ((A.powerset.filter P).card : ℚ) := by rw [← mul_pow]
    rw [h_lhs_cancel, h_rhs_combine] at h_mul_2K
    have h_base_bound : 2 * (63 / 64 : ℚ) ^ 256 ≤ 1 / 4 := by
      have h16 : (63 / 64 : ℚ) ^ 16 ≤ 4 / 5 := by norm_num
      have h256 : (63 / 64 : ℚ) ^ 256 ≤ 1 / 8 := by
        have h_eq : (63 / 64 : ℚ) ^ 256 = ((63 / 64 : ℚ) ^ 16) ^ 16 := by ring
        rw [h_eq]
        exact le_trans (pow_le_pow_left₀ (by positivity) h16 16) (by norm_num)
      linarith
    have h_pow_14 : (2 * (63 / 64 : ℚ) ^ 256) ^ K ≤ (1 / 4 : ℚ) ^ K :=
      pow_le_pow_left₀ (by positivity) h_base_bound K
    exact le_trans h_mul_2K (mul_le_mul_of_nonneg_right h_pow_14 (Nat.cast_nonneg _))

  
  let Ω₀ : Finset (Finset ℕ) := A.powerset
  let K_fn : ℕ → ℕ := fun q => (C q).card / 1024
  let E : ℕ → Finset (Finset ℕ) := fun q => Ω₀.filter (fun S => (U S q).card < K_fn q)
  let x : ℕ → ℚ := fun q => (1 / 2 : ℚ) ^ (K_fn q)
  let B : Finset ℕ → Finset (Finset ℕ) := fun S => Ω₀.filter (fun ω => ∀ k ∈ S, ω ∉ E k)

  have hΓ_sub : ∀ q ∈ Q, Γ q ⊆ Q \ {q} := fun q _ => Finset.filter_subset _ _

  have hK_ge17 : ∀ q ∈ Q, 17 ≤ K_fn q := by
    intro q hq
    have h_c := h_cap q hq
    dsimp [K_fn]
    omega

  have hx_bounds : ∀ q ∈ Q, 0 ≤ x q ∧ x q < 1 ∧ x q ≤ 1 / 131072 := by
    intro q hq
    have h17 := hK_ge17 q hq
    have h_le : (1 / 2 : ℚ) ^ (K_fn q) ≤ (1 / 2 : ℚ) ^ 17 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h17
    have h_val : (1 / 2 : ℚ) ^ 17 = 1 / 131072 := by norm_num
    refine ⟨by positivity, ?_, by linarith⟩
    linarith

  have h_bernoulli : ∀ n : ℕ, 1 - (n : ℚ) * (1 / 131072 : ℚ) ≤ (131071 / 131072 : ℚ) ^ n := by
    intro n
    induction' n with n ih
    · norm_num
    · rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have h_nonneg : 0 ≤ (n : ℚ) * (1 / 131072 : ℚ) ^ 2 := by positivity
      nlinarith

  have h_prod_Γ_ge : ∀ q ∈ Q, (1 / 4 : ℚ) ^ (K_fn q) ≤ x q * (∏ j ∈ Γ q, (1 - x j)) := by
    intro q hq
    have h_term : ∀ j ∈ Γ q, (131071 / 131072 : ℚ) ≤ 1 - x j := by
      intro j hj
      have hjQ : j ∈ Q := (Finset.mem_sdiff.mp (hΓ_sub q hq hj)).1
      have hxj := (hx_bounds j hjQ).2.2
      linarith
    have h_prod_low : (131071 / 131072 : ℚ) ^ (Γ q).card ≤ ∏ j ∈ Γ q, (1 - x j) := by
      calc (131071 / 131072 : ℚ) ^ (Γ q).card
          = ∏ _j ∈ Γ q, (131071 / 131072 : ℚ) := (Finset.prod_const (131071 / 131072 : ℚ)).symm
        _ ≤ ∏ j ∈ Γ q, (1 - x j) := Finset.prod_le_prod (fun _ _ => by norm_num) h_term
    have h_deg_K : (Γ q).card ≤ 65536 * K_fn q := by
      have hd := h_deg q hq
      have h17 := hK_ge17 q hq
      dsimp [K_fn] at h17 ⊢
      omega
    have h_pow_K : ((131071 / 131072 : ℚ) ^ 65536) ^ (K_fn q) ≤ (131071 / 131072 : ℚ) ^ (Γ q).card := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h_deg_K
    have h_65536 : (1 / 2 : ℚ) ≤ (131071 / 131072 : ℚ) ^ 65536 := by
      have h_eq_half : (1 / 2 : ℚ) = 1 - ((65536 : ℕ) : ℚ) * (1 / 131072 : ℚ) := by norm_num
      rw [h_eq_half]
      exact h_bernoulli 65536
    have h_half_K : (1 / 2 : ℚ) ^ (K_fn q) ≤ ((131071 / 131072 : ℚ) ^ 65536) ^ (K_fn q) :=
      pow_le_pow_left₀ (by norm_num) h_65536 (K_fn q)
    have h_prod_ge_x : x q ≤ ∏ j ∈ Γ q, (1 - x j) :=
      le_trans h_half_K (le_trans h_pow_K h_prod_low)
    calc (1 / 4 : ℚ) ^ (K_fn q)
        = (1 / 2 * (1 / 2) : ℚ) ^ (K_fn q) := by norm_num
      _ = x q * x q := by rw [mul_pow]
      _ ≤ x q * (∏ j ∈ Γ q, (1 - x j)) :=
          mul_le_mul_of_nonneg_left h_prod_ge_x (hx_bounds q hq).1

  have h_lll_cond : ∀ q ∈ Q, ∀ S₂ ⊆ Q \ (Γ q ∪ {q}),
      ((E q ∩ B S₂).card : ℚ) ≤ x q * (∏ j ∈ Γ q, (1 - x j)) * ((B S₂).card : ℚ) := by
    intro q hq S₂ hS₂
    let P : Finset ℕ → Prop := fun S => ∀ k ∈ S₂, S ∉ E k
    have hP_inv : ∀ j ∈ C q, ∀ S ⊆ A, ∀ T ⊆ N_A (a q j), P ((S \ N_A (a q j)) ∪ T) ↔ P S := by
      intro j hj S hSA T hTN₀
      dsimp [P]
      refine forall₂_congr (fun k hkS₂ => not_congr ?_)
      have hk_sdiff := Finset.mem_sdiff.mp (hS₂ hkS₂)
      have hkQ : k ∈ Q := hk_sdiff.1
      have hk_not_union : k ∉ Γ q ∪ {q} := hk_sdiff.2
      have hkne : k ≠ q := fun h_eq => hk_not_union (Finset.mem_union_right _ (Finset.mem_singleton.mpr h_eq))
      have hk_not_Γ : k ∉ Γ q := fun hkΓ => hk_not_union (Finset.mem_union_left _ hkΓ)
      have hW_disj : Disjoint (W q) (W k) := by
        by_contra h_nd
        exact hk_not_Γ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hkQ, Finset.notMem_singleton.mpr hkne⟩, h_nd⟩)
      have h_Uk_eq : U ((S \ N_A (a q j)) ∪ T) k = U S k := by
        dsimp [U]
        refine Finset.filter_congr (fun j' hj' => ?_)
        have hN_sub_q : N_A (a q j) ⊆ W q := (h_geom q hq j hj).2.1
        have hN_sub_k : N_A (a k j') ⊆ W k := (h_geom k hkQ j' hj').2.1
        have hN_disj : Disjoint (N_A (a q j)) (N_A (a k j')) :=
          Finset.disjoint_left.mpr (fun y hy₁ hy₂ => Finset.disjoint_left.mp hW_disj (hN_sub_q hy₁) (hN_sub_k hy₂))
        have h_inter_eq : ((S \ N_A (a q j)) ∪ T) ∩ N_A (a k j') = S ∩ N_A (a k j') := by
          ext y
          simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨hyS, _⟩ | hyT, hyNk⟩
            · exact ⟨hyS, hyNk⟩
            · exact (Finset.disjoint_left.mp hN_disj (hTN₀ hyT) hyNk).elim
          · rintro ⟨hyS, hyNk⟩
            exact ⟨Or.inl ⟨hyS, fun hyNq => Finset.disjoint_left.mp hN_disj hyNq hyNk⟩, hyNk⟩
        rw [h_inter_eq]
      have h_u_sub : (S \ N_A (a q j)) ∪ T ⊆ A :=
        Finset.union_subset (Finset.Subset.trans Finset.sdiff_subset hSA)
          (Finset.Subset.trans hTN₀ (Finset.Subset.trans (h_geom q hq j hj).2.1 (h_geom q hq j hj).2.2.1))
      simp only [E, Ω₀, Finset.mem_filter, Finset.mem_powerset, h_u_sub, hSA, true_and, h_Uk_eq]
    have h_eq_inter : E q ∩ B S₂ = A.powerset.filter (fun S => (U S q).card < K_fn q ∧ P S) := by
      ext S
      simp only [E, B, Ω₀, P, Finset.mem_inter, Finset.mem_filter]
      tauto
    have h_step := h_cond_bound q hq P hP_inv
    rw [← h_eq_inter] at h_step
    exact le_trans h_step (mul_le_mul_of_nonneg_right (h_prod_Γ_ge q hq) (Nat.cast_nonneg _))

  have hB_insert : ∀ (U₀ : Finset ℕ) (r : ℕ),
      ((B (insert r U₀)).card : ℚ) = ((B U₀).card : ℚ) - ((E r ∩ B U₀).card : ℚ) := by
    intro U₀ r
    have h_eq : B (insert r U₀) = B U₀ \ E r := by
      ext ω
      simp only [B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, forall_eq_or_imp]
      tauto
    have h_sub : E r ∩ B U₀ ⊆ B U₀ := Finset.inter_subset_right
    rw [h_eq, Finset.card_sdiff, Nat.cast_sub (Finset.card_le_card h_sub)]

  have h_sub_prod : ∀ (S₂ T : Finset ℕ),
      (∀ j ∈ T, 0 ≤ 1 - x j) →
      (∀ T' ⊆ T, ∀ j ∈ T \ T', ((E j ∩ B (T' ∪ S₂)).card : ℚ) ≤ x j * ((B (T' ∪ S₂)).card : ℚ)) →
      (∏ j ∈ T, (1 - x j)) * ((B S₂).card : ℚ) ≤ ((B (T ∪ S₂)).card : ℚ) := by
    intro S₂ T
    induction' T using Finset.induction_on with j₀ T' hj₀ ih
    · intro _ _
      simp
    · intro h_pos h_step
      have h_pos' : ∀ j ∈ T', 0 ≤ 1 - x j := fun j hj => h_pos j (Finset.mem_insert_of_mem hj)
      have h_step' : ∀ T'' ⊆ T', ∀ j ∈ T' \ T'',
          ((E j ∩ B (T'' ∪ S₂)).card : ℚ) ≤ x j * ((B (T'' ∪ S₂)).card : ℚ) := by
        intro T'' hT'' j hj
        have hj_sdiff := Finset.mem_sdiff.mp hj
        exact h_step T'' (Finset.Subset.trans hT'' (Finset.subset_insert j₀ T')) j
          (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hj_sdiff.1, hj_sdiff.2⟩)
      have h_ih := ih h_pos' h_step'
      have hj₀_pos : 0 ≤ 1 - x j₀ := h_pos j₀ (Finset.mem_insert_self j₀ T')
      have h_mul := mul_le_mul_of_nonneg_left h_ih hj₀_pos
      rw [← mul_assoc] at h_mul
      have hj₀_sdiff : j₀ ∈ insert j₀ T' \ T' :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self j₀ T', hj₀⟩
      have h_j₀_bound := h_step T' (Finset.subset_insert j₀ T') j₀ hj₀_sdiff
      have h_union : insert j₀ T' ∪ S₂ = insert j₀ (T' ∪ S₂) := Finset.insert_union j₀ T' S₂
      rw [Finset.prod_insert hj₀, h_union, hB_insert (T' ∪ S₂) j₀]
      linarith

  have h_claim_B : ∀ (m : ℕ) (S : Finset ℕ), S ⊆ Q → S.card = m →
      ∀ i ∈ Q \ S, ((E i ∩ B S).card : ℚ) ≤ x i * ((B S).card : ℚ) := by
    intro m
    induction' m using Nat.strong_induction_on with m ih
    intro S hSQ hScard i hi
    have hi_sdiff := Finset.mem_sdiff.mp hi
    have hiQ : i ∈ Q := hi_sdiff.1
    have hi_not_S : i ∉ S := hi_sdiff.2
    let S₁ := S ∩ Γ i
    let S₂ := S \ Γ i
    have hS_union : S₁ ∪ S₂ = S := by
      ext k
      simp only [S₁, S₂, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hS₁_pos : ∀ j ∈ S₁, 0 ≤ 1 - x j := by
      intro j hj
      have hjQ : j ∈ Q := hSQ (Finset.mem_of_mem_inter_left hj)
      linarith [(hx_bounds j hjQ).2.1]
    have hS₁_step : ∀ T' ⊆ S₁, ∀ j ∈ S₁ \ T',
        ((E j ∩ B (T' ∪ S₂)).card : ℚ) ≤ x j * ((B (T' ∪ S₂)).card : ℚ) := by
      intro T' hT' j hj
      have hj_sdiff := Finset.mem_sdiff.mp hj
      have hjS₁ : j ∈ S₁ := hj_sdiff.1
      have hj_not_T' : j ∉ T' := hj_sdiff.2
      have hjS : j ∈ S := Finset.mem_of_mem_inter_left hjS₁
      have hjΓ : j ∈ Γ i := Finset.mem_of_mem_inter_right hjS₁
      have hU_sub_S : T' ∪ S₂ ⊆ S.erase j := by
        intro k hk
        rcases Finset.mem_union.mp hk with hkT' | hkS₂
        · have hkS : k ∈ S := Finset.mem_of_mem_inter_left (hT' hkT')
          have hkne : k ≠ j := fun h_eq => hj_not_T' (h_eq ▸ hkT')
          exact Finset.mem_erase.mpr ⟨hkne, hkS⟩
        · have hk_sdiff := Finset.mem_sdiff.mp hkS₂
          have hkne : k ≠ j := fun h_eq => hk_sdiff.2 (h_eq ▸ hjΓ)
          exact Finset.mem_erase.mpr ⟨hkne, hk_sdiff.1⟩
      have hU_sub_Q : T' ∪ S₂ ⊆ Q :=
        Finset.Subset.trans hU_sub_S (Finset.Subset.trans (Finset.erase_subset j S) hSQ)
      have hU_card_lt : (T' ∪ S₂).card < m := by
        have h1 := Finset.card_le_card hU_sub_S
        have h2 := Finset.card_erase_lt_of_mem hjS
        omega
      have hj_in_Q_sdiff : j ∈ Q \ (T' ∪ S₂) := by
        refine Finset.mem_sdiff.mpr ⟨hSQ hjS, ?_⟩
        intro hj_in
        exact (Finset.mem_erase.mp (hU_sub_S hj_in)).1 rfl
      exact ih (T' ∪ S₂).card hU_card_lt (T' ∪ S₂) hU_sub_Q rfl j hj_in_Q_sdiff
    have h_B_S₁ := h_sub_prod S₂ S₁ hS₁_pos hS₁_step
    rw [hS_union] at h_B_S₁
    have h_prod_mono : (∏ j ∈ Γ i, (1 - x j)) ≤ (∏ j ∈ S₁, (1 - x j)) := by
      have h_eq : Γ i = S₁ ∪ (Γ i \ S) := by
        ext k
        simp only [S₁, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have h_disj : Disjoint S₁ (Γ i \ S) := by
        rw [Finset.disjoint_left]
        intro k hk₁ hk₂
        exact (Finset.mem_sdiff.mp hk₂).2 (Finset.mem_of_mem_inter_left hk₁)
      rw [h_eq, Finset.prod_union h_disj]
      have h_le_one : (∏ j ∈ Γ i \ S, (1 - x j)) ≤ 1 := by
        apply Finset.prod_le_one
        · intro j hj
          have hjQ : j ∈ Q := (Finset.mem_sdiff.mp (hΓ_sub i hiQ (Finset.mem_sdiff.mp hj).1)).1
          linarith [(hx_bounds j hjQ).2.1]
        · intro j hj
          have hjQ : j ∈ Q := (Finset.mem_sdiff.mp (hΓ_sub i hiQ (Finset.mem_sdiff.mp hj).1)).1
          linarith [(hx_bounds j hjQ).1]
      have h_nonneg : 0 ≤ ∏ j ∈ S₁, (1 - x j) :=
        Finset.prod_nonneg (fun j hj => hS₁_pos j hj)
      nlinarith
    have h_B_Γ : (∏ j ∈ Γ i, (1 - x j)) * ((B S₂).card : ℚ) ≤ ((B S).card : ℚ) := by
      have h_mul := mul_le_mul_of_nonneg_right h_prod_mono (Nat.cast_nonneg (B S₂).card)
      exact le_trans h_mul h_B_S₁
    have hS₂_sub : S₂ ⊆ Q \ (Γ i ∪ {i}) := by
      intro k hk
      have hk_sdiff := Finset.mem_sdiff.mp hk
      refine Finset.mem_sdiff.mpr ⟨hSQ hk_sdiff.1, ?_⟩
      intro hk_in
      rcases Finset.mem_union.mp hk_in with hkΓ | hki
      · exact hk_sdiff.2 hkΓ
      · rw [Finset.mem_singleton] at hki
        exact hi_not_S (hki ▸ hk_sdiff.1)
    have h_cond_i := h_lll_cond i hiQ S₂ hS₂_sub
    have h_BS_sub : E i ∩ B S ⊆ E i ∩ B S₂ := by
      intro ω hω
      simp only [B, Finset.mem_inter, Finset.mem_filter] at hω ⊢
      exact ⟨hω.1, hω.2.1, fun k hk => hω.2.2 k (Finset.mem_sdiff.mp hk).1⟩
    have h_card_mono : ((E i ∩ B S).card : ℚ) ≤ ((E i ∩ B S₂).card : ℚ) :=
      Nat.cast_le.mpr (Finset.card_le_card h_BS_sub)
    have hxi_nonneg : 0 ≤ x i := (hx_bounds i hiQ).1
    have h_mul_xi := mul_le_mul_of_nonneg_left h_B_Γ hxi_nonneg
    rw [← mul_assoc] at h_mul_xi
    exact le_trans h_card_mono (le_trans h_cond_i h_mul_xi)

  have hQ_pos : ∀ j ∈ Q, 0 ≤ 1 - x j := fun j hj => by linarith [(hx_bounds j hj).2.1]
  have hQ_step : ∀ T' ⊆ Q, ∀ j ∈ Q \ T',
      ((E j ∩ B (T' ∪ ∅)).card : ℚ) ≤ x j * ((B (T' ∪ ∅)).card : ℚ) := by
    intro T' hT' j hj
    rw [Finset.union_empty]
    exact h_claim_B T'.card T' hT' rfl j hj
  have h_final := h_sub_prod ∅ Q hQ_pos hQ_step
  rw [Finset.union_empty] at h_final
  have hB_empty : B ∅ = Ω₀ := by
    ext ω
    simp [B]
  rw [hB_empty] at h_final
  have h_prod_pos : 0 < ∏ j ∈ Q, (1 - x j) :=
    Finset.prod_pos (fun j hj => by linarith [(hx_bounds j hj).2.1])
  have hΩ₀_nonempty : Ω₀.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset A)⟩
  have hΩ₀_pos : (0 : ℚ) < (Ω₀.card : ℚ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hΩ₀_nonempty)
  have h_BQ_pos : (0 : ℚ) < ((B Q).card : ℚ) :=
    lt_of_lt_of_le (mul_pos h_prod_pos hΩ₀_pos) h_final
  obtain ⟨S₀, hS₀⟩ := Finset.card_pos.mp (Nat.cast_pos.mp h_BQ_pos)
  refine ⟨U S₀, ?_, h_det_sep S₀⟩
  intro q hq
  refine ⟨Finset.filter_subset _ _, ?_⟩
  have hS₀_not_E : S₀ ∉ E q := (Finset.mem_filter.mp hS₀).2 q hq
  have hS₀_Ω : S₀ ∈ Ω₀ := (Finset.mem_filter.mp hS₀).1
  by_contra h_lt
  push_neg at h_lt
  exact hS₀_not_E (Finset.mem_filter.mpr ⟨hS₀_Ω, h_lt⟩)

theorem simultaneous_good_subset_thinning_existence (q : ℕ) (hq : 2 ^ 128 ≤ q)
    (U : Finset ℕ) (hU_card : q / (2 ^ 20 * (Nat.log 2 q + 1)) ≤ U.card)
    (Δ_q : Finset ℤ) (hΔ_card : Δ_q.card ≤ q)
    (G : ℤ → Finset ℕ)
    (hG_sub : ∀ δ₀ ∈ Δ_q, G δ₀ ⊆ U)
    (hG_card : ∀ δ₀ ∈ Δ_q, 7 * U.card / 8 ≤ (G δ₀).card) :
    ∃ V ⊆ U,
      V.card ≤ 2 ^ 55 * (Nat.log 2 q + 1) ^ 3 ∧
      ∀ δ₀ ∈ Δ_q, 2 ^ 53 * (Nat.log 2 q + 1) ^ 3 ≤ (V ∩ G δ₀).card :=
by
  classical
  set L_q := Nat.log 2 q + 1
  generalize hK_def : 2 ^ 52 * L_q ^ 3 = K
  set h := 8 * K
  have hq_pos : 0 < q := by omega
  have hk_ge : 128 ≤ Nat.log 2 q := by
    have h1 := Nat.log_mono_right (b := 2) hq
    rwa [Nat.log_pow (by decide : 1 < 2)] at h1
  have h2k_le : 2 ^ (Nat.log 2 q) ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hL_pos : 1 ≤ L_q ^ 3 := Nat.one_le_pow 3 L_q (by omega)
  have h_U_large : 16 * h + 56 ≤ U.card := by
    set m := Nat.log 2 q - 128
    have hm_eq : Nat.log 2 q = 128 + m := by omega
    have hL_eq : L_q = m + 129 := by omega
    set x := m / 8
    have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
    have h2x_pos : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    have hL_le : L_q ≤ 2 ^ 8 * 2 ^ x := by omega
    have hL4 : L_q ^ 4 ≤ (2 ^ 8 * 2 ^ x) ^ 4 := Nat.pow_le_pow_left hL_le 4
    have h_pow_eq : (2 ^ 8 * 2 ^ x) ^ 4 = 2 ^ (32 + 4 * x) := by
      rw [← Nat.pow_add, ← Nat.pow_mul]
      ring_nf
    rw [h_pow_eq] at hL4
    have h_16h : 16 * h + 56 ≤ 2 ^ 60 * L_q ^ 3 := by
      dsimp [h]
      rw [← hK_def]
      omega
    have h_mul : (2 ^ 20 * L_q) * (16 * h + 56) ≤ 2 ^ (112 + 4 * x) := by
      calc (2 ^ 20 * L_q) * (16 * h + 56)
          ≤ (2 ^ 20 * L_q) * (2 ^ 60 * L_q ^ 3) := Nat.mul_le_mul_left _ h_16h
        _ = 2 ^ 80 * L_q ^ 4 := by ring
        _ ≤ 2 ^ 80 * 2 ^ (32 + 4 * x) := Nat.mul_le_mul_left _ hL4
        _ = 2 ^ (112 + 4 * x) := by rw [← Nat.pow_add]; ring_nf
    have h_exp_le : 112 + 4 * x ≤ Nat.log 2 q := by omega
    have h_le_q : (2 ^ 20 * L_q) * (16 * h + 56) ≤ q :=
      le_trans h_mul (le_trans (Nat.pow_le_pow_right (by decide) h_exp_le) h2k_le)
    have h_div : 16 * h + 56 ≤ q / (2 ^ 20 * L_q) :=
      (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith)
    exact le_trans h_div hU_card
  let B : ℤ → Finset ℕ := fun δ₀ => U \ G δ₀
  have hB_card : ∀ δ₀ ∈ Δ_q, 4 * (B δ₀).card ≤ U.card - h := by
    intro δ₀ hδ₀
    have h_sub := hG_sub δ₀ hδ₀
    have h_card := hG_card δ₀ hδ₀
    have h_le : (G δ₀).card ≤ U.card := Finset.card_le_card h_sub
    have h_sdiff : (B δ₀).card = U.card - (G δ₀).card := by
      dsimp [B]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h_sub]
    omega
  let Φ : Finset ℕ → ℚ := fun S => ∑ δ₀ ∈ Δ_q, (2 : ℚ) ^ (S ∩ B δ₀).card
  have h_step : ∀ (t : ℕ) (S : Finset ℕ), S ⊆ U → S.card = t → t < h →
      ∃ x ∈ U \ S, Φ (insert x S) ≤ (5 / 4 : ℚ) * Φ S := by
    intro t S hSU hScard hth
    let U' := U \ S
    have hU'_card : U'.card = U.card - t := by
      dsimp [U']
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSU, hScard]
    have hU'_pos : 0 < U'.card := by omega
    have hU'_nonempty : U'.Nonempty := Finset.card_pos.mp hU'_pos
    have h_term_eq : ∀ x ∈ U', ∀ δ₀ ∈ Δ_q,
        (2 : ℚ) ^ ((insert x S) ∩ B δ₀).card =
          (2 : ℚ) ^ (S ∩ B δ₀).card * (1 + if x ∈ B δ₀ then (1 : ℚ) else 0) := by
      intro x hx δ₀ _
      have hx_not_S : x ∉ S := (Finset.mem_sdiff.mp hx).2
      by_cases hxB : x ∈ B δ₀
      · have h_inter : (insert x S) ∩ B δ₀ = insert x (S ∩ B δ₀) :=
          Finset.insert_inter_of_mem hxB
        have hx_not_inter : x ∉ S ∩ B δ₀ := fun h_in => hx_not_S (Finset.mem_inter.mp h_in).1
        rw [h_inter, Finset.card_insert_of_notMem hx_not_inter, if_pos hxB, pow_succ]
        ring
      · have h_inter : (insert x S) ∩ B δ₀ = S ∩ B δ₀ :=
          Finset.insert_inter_of_notMem hxB
        rw [h_inter, if_neg hxB]
        ring
    have h_sum_x : ∀ δ₀ ∈ Δ_q,
        ∑ x ∈ U', (2 : ℚ) ^ ((insert x S) ∩ B δ₀).card ≤
          (2 : ℚ) ^ (S ∩ B δ₀).card * ((5 / 4 : ℚ) * (U'.card : ℚ)) := by
      intro δ₀ hδ₀
      have h_congr : ∑ x ∈ U', (2 : ℚ) ^ ((insert x S) ∩ B δ₀).card =
          (2 : ℚ) ^ (S ∩ B δ₀).card * ∑ x ∈ U', (1 + if x ∈ B δ₀ then (1 : ℚ) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x hx => h_term_eq x hx δ₀ hδ₀)
      rw [h_congr]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_boole,
        Finset.filter_mem_eq_inter]
      have h_inter_le : (U' ∩ B δ₀).card ≤ (B δ₀).card :=
        Finset.card_le_card Finset.inter_subset_right
      have h_4le : 4 * (U' ∩ B δ₀).card ≤ U'.card := by
        have := hB_card δ₀ hδ₀
        omega
      have h_4le_q : 4 * ((U' ∩ B δ₀).card : ℚ) ≤ (U'.card : ℚ) := by exact_mod_cast h_4le
      linarith
    have h_total_sum : ∑ x ∈ U', Φ (insert x S) ≤ ∑ x ∈ U', (5 / 4 : ℚ) * Φ S := by
      dsimp [Φ]
      rw [Finset.sum_comm]
      calc ∑ y ∈ Δ_q, ∑ x ∈ U', (2 : ℚ) ^ ((insert x S) ∩ B y).card
          ≤ ∑ y ∈ Δ_q, (2 : ℚ) ^ (S ∩ B y).card * ((5 / 4 : ℚ) * (U'.card : ℚ)) :=
            Finset.sum_le_sum h_sum_x
        _ = (U'.card : ℚ) * ((5 / 4 : ℚ) * ∑ y ∈ Δ_q, (2 : ℚ) ^ (S ∩ B y).card) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun y _ => by ring)
        _ = ∑ x ∈ U', (5 / 4 : ℚ) * ∑ y ∈ Δ_q, (2 : ℚ) ^ (S ∩ B y).card := by
            rw [Finset.sum_const, nsmul_eq_mul]
    exact Finset.exists_le_of_sum_le hU'_nonempty h_total_sum
  have h_ind : ∀ t ≤ h, ∃ S ⊆ U, S.card = t ∧ Φ S ≤ (5 / 4 : ℚ) ^ t * Φ ∅ := by
    intro t
    induction' t with t ih
    · intro _
      refine ⟨∅, Finset.empty_subset U, Finset.card_empty, by simp⟩
    · intro ht
      obtain ⟨S, hSU, hScard, hSΦ⟩ := ih (by omega)
      obtain ⟨x, hxU', hxΦ⟩ := h_step t S hSU hScard (by omega)
      have hxU : x ∈ U := (Finset.mem_sdiff.mp hxU').1
      have hx_not_S : x ∉ S := (Finset.mem_sdiff.mp hxU').2
      refine ⟨insert x S, Finset.insert_subset hxU hSU, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hx_not_S, hScard]
      · calc Φ (insert x S) ≤ (5 / 4 : ℚ) * Φ S := hxΦ
          _ ≤ (5 / 4 : ℚ) * ((5 / 4 : ℚ) ^ t * Φ ∅) :=
              mul_le_mul_of_nonneg_left hSΦ (by positivity)
          _ = (5 / 4 : ℚ) ^ (t + 1) * Φ ∅ := by rw [pow_succ']; ring
  obtain ⟨V, hVU, hVcard, hVΦ⟩ := h_ind h (le_refl h)
  refine ⟨V, hVU, ?_, ?_⟩
  · rw [hVcard]
    dsimp [h]
    rw [← hK_def]
    omega
  · intro δ₀ hδ₀
    have hΦ_empty : Φ ∅ = (Δ_q.card : ℚ) := by
      dsimp [Φ]
      simp [Finset.sum_const, nsmul_eq_mul]
    have h_q_lt_2L : q < 2 ^ L_q := Nat.lt_pow_succ_log_self (by decide) q
    have hL_le_K : L_q ≤ K := by
      have h_pos2 : 1 ≤ 2 ^ 52 * L_q ^ 2 :=
        Nat.mul_pos (by positivity) (Nat.one_le_pow 2 L_q (by omega))
      calc L_q = 1 * L_q := (one_mul L_q).symm
        _ ≤ (2 ^ 52 * L_q ^ 2) * L_q := Nat.mul_le_mul_right L_q h_pos2
        _ = 2 ^ 52 * L_q ^ 3 := by ring
        _ = K := hK_def
    have h_q_lt_2K : (Δ_q.card : ℚ) < (2 : ℚ) ^ K := by
      have h1 : Δ_q.card < 2 ^ K :=
        lt_of_le_of_lt hΔ_card (lt_of_lt_of_le h_q_lt_2L (Nat.pow_le_pow_right (by decide) hL_le_K))
      exact_mod_cast h1
    have h_54_8 : ((5 / 4 : ℚ) ^ 8) ≤ (2 : ℚ) ^ 3 := by norm_num
    have h_54_h : (5 / 4 : ℚ) ^ h ≤ (2 : ℚ) ^ (3 * K) := by
      dsimp [h]
      rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (by positivity) h_54_8 K
    have hVΦ_lt : Φ V < (2 : ℚ) ^ (4 * K) := by
      rw [hΦ_empty] at hVΦ
      have h_pos_54 : (0 : ℚ) < (5 / 4 : ℚ) ^ h := by positivity
      calc Φ V ≤ (5 / 4 : ℚ) ^ h * (Δ_q.card : ℚ) := hVΦ
        _ < (5 / 4 : ℚ) ^ h * (2 : ℚ) ^ K :=
            mul_lt_mul_of_pos_left h_q_lt_2K h_pos_54
        _ ≤ (2 : ℚ) ^ (3 * K) * (2 : ℚ) ^ K :=
            mul_le_mul_of_nonneg_right h_54_h (by positivity)
        _ = (2 : ℚ) ^ (4 * K) := by rw [← pow_add]; ring_nf
    have h_single_le : (2 : ℚ) ^ (V ∩ B δ₀).card ≤ Φ V := by
      dsimp [Φ]
      exact Finset.single_le_sum (f := fun y => (2 : ℚ) ^ (V ∩ B y).card) (fun y _ => by positivity) hδ₀
    have h_pow_lt : (2 : ℚ) ^ (V ∩ B δ₀).card < (2 : ℚ) ^ (4 * K) :=
      lt_of_le_of_lt h_single_le hVΦ_lt
    have h_card_lt : (V ∩ B δ₀).card < 4 * K := by
      by_contra! h_ge
      have h_pow_ge : (2 : ℚ) ^ (4 * K) ≤ (2 : ℚ) ^ (V ∩ B δ₀).card :=
        pow_le_pow_right₀ (by norm_num) h_ge
      exact not_lt_of_ge h_pow_ge h_pow_lt
    have h_part : (V ∩ G δ₀).card + (V ∩ B δ₀).card = V.card := by
      dsimp [B]
      have h_eq : V ∩ (U \ G δ₀) = V \ (V ∩ G δ₀) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro ⟨hxV, _, hxG⟩
          exact ⟨hxV, fun ⟨_, hxG'⟩ => hxG hxG'⟩
        · rintro ⟨hxV, hxVG⟩
          exact ⟨hxV, hVU hxV, fun hxG => hxVG ⟨hxV, hxG⟩⟩
      rw [h_eq, add_comm, Finset.card_sdiff_add_card_eq_card Finset.inter_subset_left]
    have h_VG_gt : 4 * K < (V ∩ G δ₀).card := by omega
    rw [← hK_def] at h_VG_gt
    omega

theorem finite_horizon_simultaneous_thinning_existence (B : ℕ) (m_res : ℕ → ℕ) (I_res : ℕ → ℕ → ℕ × ℕ)
    (hB : 2 ^ 128 ≤ B)
    (h_bounds : ∀ q > B, ∀ j < m_res q,
      q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ (I_res q j).1 ∧
      (I_res q j).2 = (I_res q j).1 + 1 ∧
      (I_res q j).2 ≤ q ^ 2 / 2 ∧
      w_Icc (I_res q j).1 (I_res q j).2 ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2)
    (h_sep : ∀ q > B, ∀ j₁ < m_res q, ∀ j₂ < m_res q, j₁ ≠ j₂ →
      (I_res q j₁).2 + 1 < (I_res q j₂).1 ∨ (I_res q j₂).2 + 1 < (I_res q j₁).1)
    (h_dist : ∀ q₁ > B, ∀ q₂ > B, ∀ j₁ < m_res q₁, ∀ j₂ < m_res q₂,
      (q₁ ≠ q₂ ∨ j₁ ≠ j₂) → (I_res q₁ j₁).1 ≠ (I_res q₂ j₂).1)
    (h_lcm : ∀ q > B, ∀ j < m_res q,
      ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I_res q j).1 (I_res q j).2).den = 1)
    (h_phase : ∀ q > B,
      (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189 → m_res q = 0) ∧
      (¬ (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189) →
        m_res q = q / (512 * (Nat.log 2 q + 1)) ∧
        ∃ Δ_q : Finset ℤ, Δ_q.card ≤ q ∧
          (∀ δ : ℤ,
            ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
            ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
            ∃ δ₀ ∈ Δ_q, ∀ j < m_res q,
              (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 =
              (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) ∧
          (∀ δ₀ ∈ Δ_q, ∀ U ⊆ Finset.range (m_res q), m_res q / 2048 ≤ U.card →
            7 * U.card / 8 ≤
              (U.filter (fun j =>
                (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
                  (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2)).card)))
    (M : ℕ) :
    ∃ V_M : ℕ → Finset ℕ,
      (∀ q : ℕ, V_M q ⊆ Finset.range (m_res q) ∧ (V_M q).card ≤ 2 ^ 55 * (Nat.log 2 q + 1) ^ 3) ∧
      (∀ q₁ ∈ Finset.Ioc B M, ∀ q₂ ∈ Finset.Ioc B M, ∀ j₁ ∈ V_M q₁, ∀ j₂ ∈ V_M q₂,
        (q₁ ≠ q₂ ∨ j₁ ≠ j₂) →
        (I_res q₁ j₁).2 + 1 < (I_res q₂ j₂).1 ∨ (I_res q₂ j₂).2 + 1 < (I_res q₁ j₁).1) ∧
      (∀ q ∈ Finset.Ioc B M, ∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        16 * Real.log (q : ℝ) ≤
          ∑ j ∈ V_M q,
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) :=
by
  classical
  
  have h_stride : ∀ (f : ℕ → ℕ) (n : ℕ) (S : Finset ℕ), S.card = n →
      (∀ j₁ ∈ S, ∀ j₂ ∈ S, j₁ ≠ j₂ → f j₁ + 2 < f j₂ ∨ f j₂ + 2 < f j₁) →
      ∃ C ⊆ S, (S.card + 1) / 2 ≤ C.card ∧
        ∀ j₁ ∈ C, ∀ j₂ ∈ C, j₁ ≠ j₂ → f j₁ + 5 < f j₂ ∨ f j₂ + 5 < f j₁ := by
    intro f n
    induction' n using Nat.strong_induction_on with n ih
    intro S hScard h_sep_S
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · refine ⟨S, Finset.Subset.rfl, by omega, ?_⟩
      intro j₁ hj₁ j₂ hj₂ hne
      have h_le : S.card ≤ 1 := by omega
      have h_eq := Finset.card_le_one.mp h_le j₁ hj₁ j₂ hj₂
      exact (hne h_eq).elim
    · have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x₀, hx₀S, hx₀_min⟩ := Finset.exists_min_image S f hS_nonempty
      let S₁ := S.erase x₀
      have hS₁_card : S₁.card = n - 1 := by
        rw [Finset.card_erase_of_mem hx₀S, hScard]
      have hS₁_nonempty : S₁.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x₁, hx₁S₁, hx₁_min⟩ := Finset.exists_min_image S₁ f hS₁_nonempty
      have hx₁S : x₁ ∈ S := Finset.mem_of_mem_erase hx₁S₁
      have hx₁_ne_x₀ : x₁ ≠ x₀ := Finset.ne_of_mem_erase hx₁S₁
      have h_fx₀_fx₁ : f x₀ + 2 < f x₁ := by
        have h_le := hx₀_min x₁ hx₁S
        have h_or := h_sep_S x₀ hx₀S x₁ hx₁S hx₁_ne_x₀.symm
        omega
      let S₂ := S₁.erase x₁
      have hS₂_card : S₂.card = n - 2 := by
        rw [Finset.card_erase_of_mem hx₁S₁, hS₁_card]
        omega
      have hS₂_sub_S : S₂ ⊆ S :=
        Finset.Subset.trans (Finset.erase_subset x₁ S₁) (Finset.erase_subset x₀ S)
      have h_sep_S₂ : ∀ j₁ ∈ S₂, ∀ j₂ ∈ S₂, j₁ ≠ j₂ → f j₁ + 2 < f j₂ ∨ f j₂ + 2 < f j₁ :=
        fun j₁ hj₁ j₂ hj₂ hne => h_sep_S j₁ (hS₂_sub_S hj₁) j₂ (hS₂_sub_S hj₂) hne
      obtain ⟨C', hC'_sub, hC'_card, hC'_sep⟩ := ih (n - 2) (by omega) S₂ hS₂_card h_sep_S₂
      refine ⟨insert x₀ C', ?_, ?_, ?_⟩
      · rw [Finset.insert_subset_iff]
        exact ⟨hx₀S, Finset.Subset.trans hC'_sub hS₂_sub_S⟩
      · have hx₀_not_C' : x₀ ∉ C' := by
          intro h_in
          have h_in_S₁ : x₀ ∈ S₁ := Finset.mem_of_mem_erase (hC'_sub h_in)
          exact Finset.notMem_erase x₀ S h_in_S₁
        rw [Finset.card_insert_of_notMem hx₀_not_C']
        omega
      · intro j₁ hj₁ j₂ hj₂ hne
        have h_gap : ∀ z ∈ C', f x₀ + 5 < f z := by
          intro z hz
          have hz_S₂ : z ∈ S₂ := hC'_sub hz
          have hz_S₁ : z ∈ S₁ := Finset.mem_of_mem_erase hz_S₂
          have hz_ne_x₁ : z ≠ x₁ := Finset.ne_of_mem_erase hz_S₂
          have hz_S : z ∈ S := hS₂_sub_S hz_S₂
          have h_le := hx₁_min z hz_S₁
          have h_or := h_sep_S x₁ hx₁S z hz_S hz_ne_x₁.symm
          omega
        rcases Finset.mem_insert.mp hj₁ with rfl | hj₁C'
        · rcases Finset.mem_insert.mp hj₂ with rfl | hj₂C'
          · exact (hne rfl).elim
          · left; exact h_gap j₂ hj₂C'
        · rcases Finset.mem_insert.mp hj₂ with rfl | hj₂C'
          · right; exact h_gap j₁ hj₁C'
          · exact hC'_sep j₁ hj₁C' j₂ hj₂C' hne

  
  let Q : Finset ℕ := (Finset.Ioc B M).filter (fun q =>
    ¬ (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189))
  let a : ℕ → ℕ → ℕ := fun q j => (I_res q j).1

  have hQ_gt_B : ∀ q ∈ Q, B < q := by
    intro q hq
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1

  have hQ_not_dvd : ∀ q ∈ Q,
      ¬ (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189) := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2

  have h_a_sep : ∀ q ∈ Q, ∀ j₁ ∈ Finset.range (m_res q), ∀ j₂ ∈ Finset.range (m_res q),
      j₁ ≠ j₂ → a q j₁ + 2 < a q j₂ ∨ a q j₂ + 2 < a q j₁ := by
    intro q hq j₁ hj₁ j₂ hj₂ hne
    have hqB := hQ_gt_B q hq
    have hj₁_lt := Finset.mem_range.mp hj₁
    have hj₂_lt := Finset.mem_range.mp hj₂
    have hb₁ := (h_bounds q hqB j₁ hj₁_lt).2.1
    have hb₂ := (h_bounds q hqB j₂ hj₂_lt).2.1
    have hs := h_sep q hqB j₁ hj₁_lt j₂ hj₂_lt hne
    dsimp [a]
    omega

  have h_C_ex : ∀ q ∈ Q, ∃ C_q ⊆ Finset.range (m_res q),
      (m_res q + 1) / 2 ≤ C_q.card ∧
      ∀ j₁ ∈ C_q, ∀ j₂ ∈ C_q, j₁ ≠ j₂ → a q j₁ + 5 < a q j₂ ∨ a q j₂ + 5 < a q j₁ := by
    intro q hq
    obtain ⟨C_q, hC_sub, hC_card, hC_sep⟩ :=
      h_stride (a q) (m_res q) (Finset.range (m_res q)) (Finset.card_range (m_res q)) (h_a_sep q hq)
    rw [Finset.card_range] at hC_card
    exact ⟨C_q, hC_sub, hC_card, hC_sep⟩

  let C : ℕ → Finset ℕ := fun q =>
    if hq : q ∈ Q then Classical.choose (h_C_ex q hq) else ∅

  have hC_sub : ∀ q ∈ Q, C q ⊆ Finset.range (m_res q) := by
    intro q hq
    dsimp [C]
    rw [dif_pos hq]
    exact (Classical.choose_spec (h_C_ex q hq)).1

  have hC_card_half : ∀ q ∈ Q, (m_res q + 1) / 2 ≤ (C q).card := by
    intro q hq
    dsimp [C]
    rw [dif_pos hq]
    exact (Classical.choose_spec (h_C_ex q hq)).2.1

  have hC_sep : ∀ q ∈ Q, ∀ j₁ ∈ C q, ∀ j₂ ∈ C q, j₁ ≠ j₂ →
      a q j₁ + 5 < a q j₂ ∨ a q j₂ + 5 < a q j₁ := by
    intro q hq
    dsimp [C]
    rw [dif_pos hq]
    exact (Classical.choose_spec (h_C_ex q hq)).2.2

  
  have hC_cap : ∀ q ∈ Q, 2 ^ 37 ≤ (C q).card := by
    intro q hq
    have hqB := hQ_gt_B q hq
    have hq_128 : 2 ^ 128 ≤ q := le_trans hB (le_of_lt hqB)
    have hm_eq : m_res q = q / (512 * (Nat.log 2 q + 1)) :=
      ((h_phase q hqB).2 (hQ_not_dvd q hq)).1
    set k := Nat.log 2 q
    have hk_ge : 128 ≤ k := by
      have h1 := Nat.log_mono_right (b := 2) hq_128
      rwa [Nat.log_pow (by decide : 1 < 2)] at h1
    have h2k_le : 2 ^ k ≤ q := Nat.pow_log_le_self 2 (by omega)
    set m := k - 128
    set x := m / 8
    have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
    have h2x_pos : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    have hL_le : k + 1 ≤ 2 ^ 8 * 2 ^ x := by omega
    have h_mul : (512 * (k + 1)) * 2 ^ 38 ≤ 2 ^ (55 + x) := by
      calc (512 * (k + 1)) * 2 ^ 38
          = 2 ^ 47 * (k + 1) := by ring
        _ ≤ 2 ^ 47 * (2 ^ 8 * 2 ^ x) := Nat.mul_le_mul_left _ hL_le
        _ = 2 ^ (55 + x) := by rw [← Nat.pow_add, ← Nat.pow_add]; ring_nf
    have h_exp_le : 55 + x ≤ k := by omega
    have h_le_q : (512 * (k + 1)) * 2 ^ 38 ≤ q :=
      le_trans h_mul (le_trans (Nat.pow_le_pow_right (by decide) h_exp_le) h2k_le)
    have hm_ge : 2 ^ 38 ≤ m_res q := by
      rw [hm_eq]
      exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith)
    have h_half : 2 ^ 37 ≤ (m_res q + 1) / 2 := by omega
    exact le_trans h_half (hC_card_half q hq)

  have hC_inj : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ j₁ ∈ C q₁, ∀ j₂ ∈ C q₂,
      (q₁ ≠ q₂ ∨ j₁ ≠ j₂) → a q₁ j₁ ≠ a q₂ j₂ := by
    intro q₁ hq₁ q₂ hq₂ j₁ hj₁ j₂ hj₂ hne
    exact h_dist q₁ (hQ_gt_B q₁ hq₁) q₂ (hQ_gt_B q₂ hq₂)
      j₁ (Finset.mem_range.mp (hC_sub q₁ hq₁ hj₁))
      j₂ (Finset.mem_range.mp (hC_sub q₂ hq₂ hj₂)) hne

  
  obtain ⟨U_M, hU_M_props, hU_M_sep⟩ :=
    bounded_degree_simultaneous_independent_thinning Q C a hC_cap hC_inj hC_sep

  
  have h_V_act_ex : ∀ q ∈ Q, ∃ V ⊆ U_M q,
      V.card ≤ 2 ^ 55 * (Nat.log 2 q + 1) ^ 3 ∧
      (∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        16 * Real.log (q : ℝ) ≤
          ∑ j ∈ V,
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) := by
    intro q hq
    have hqB := hQ_gt_B q hq
    have hq_128 : 2 ^ 128 ≤ q := le_trans hB (le_of_lt hqB)
    obtain ⟨hm_eq, Δ_q, hΔ_card, h_rep, h_good_dens⟩ := (h_phase q hqB).2 (hQ_not_dvd q hq)
    have hU_sub_C : U_M q ⊆ C q := (hU_M_props q hq).1
    have hU_sub_m : U_M q ⊆ Finset.range (m_res q) := Finset.Subset.trans hU_sub_C (hC_sub q hq)
    have hU_card_C : (C q).card / 1024 ≤ (U_M q).card := (hU_M_props q hq).2
    have hC_half := hC_card_half q hq
    have hU_card_m : m_res q / 2048 ≤ (U_M q).card := by omega
    have hU_card_q : q / (2 ^ 20 * (Nat.log 2 q + 1)) ≤ (U_M q).card := by
      have h_mul_eq : 512 * (Nat.log 2 q + 1) * 2048 = 2 ^ 20 * (Nat.log 2 q + 1) := by omega
      have h_div_eq : m_res q / 2048 = q / (2 ^ 20 * (Nat.log 2 q + 1)) := by
        rw [hm_eq, Nat.div_div_eq_div_mul, h_mul_eq]
      rwa [← h_div_eq]
    let G : ℤ → Finset ℕ := fun δ₀ =>
      (U_M q).filter (fun j =>
        (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
          (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2)
    have hG_sub : ∀ δ₀ ∈ Δ_q, G δ₀ ⊆ U_M q := fun _ _ => Finset.filter_subset _ _
    have hG_card : ∀ δ₀ ∈ Δ_q, 7 * (U_M q).card / 8 ≤ (G δ₀).card :=
      fun δ₀ hδ₀ => h_good_dens δ₀ hδ₀ (U_M q) hU_sub_m hU_card_m
    obtain ⟨V, hVU, hVcard, hV_inter⟩ :=
      simultaneous_good_subset_thinning_existence q hq_128 (U_M q) hU_card_q Δ_q hΔ_card G hG_sub hG_card
    refine ⟨V, hVU, hVcard, ?_⟩
    
    intro δ h_dvd1 h_dvd2
    obtain ⟨δ₀, hδ₀_mem, hδ₀_eq⟩ := h_rep δ h_dvd1 h_dvd2
    have h_sum_eq : ∑ j ∈ V,
        (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 =
        ∑ j ∈ V,
        (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      exact hδ₀_eq j (Finset.mem_range.mp (hU_sub_m (hVU hj)))
    rw [h_sum_eq]
    have h_sub : V ∩ G δ₀ ⊆ V := Finset.inter_subset_left
    have h_sum_sub : ∑ j ∈ V ∩ G δ₀,
        (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 ≤
        ∑ j ∈ V,
        (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun j _ _ => sq_nonneg _)
    have h_term_low : ∀ j ∈ V ∩ G δ₀,
        (1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2) ≤
          (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 := by
      intro j hj
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
    have h_sum_card := Finset.card_nsmul_le_sum (V ∩ G δ₀)
      (fun j => (Real.sin (Real.pi * (δ₀ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2)
      ((1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2)) h_term_low
    rw [nsmul_eq_mul] at h_sum_card
    have h_card_ge : (2 ^ 53 * (Nat.log 2 q + 1 : ℝ) ^ 3) ≤ ((V ∩ G δ₀).card : ℝ) := by
      have h_nat : 2 ^ 53 * (Nat.log 2 q + 1) ^ 3 ≤ (V ∩ G δ₀).card := hV_inter δ₀ hδ₀_mem
      exact_mod_cast h_nat
    have h_L_pos : (0 : ℝ) < (Nat.log 2 q + 1 : ℝ) := by positivity
    have h_prod_ge : 32 * (Nat.log 2 q + 1 : ℝ) ≤
        ((V ∩ G δ₀).card : ℝ) * ((1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2)) := by
      calc 32 * (Nat.log 2 q + 1 : ℝ)
          = (2 ^ 53 * (Nat.log 2 q + 1 : ℝ) ^ 3) * ((1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2)) := by
            field_simp [ne_of_gt h_L_pos]
            ring
        _ ≤ ((V ∩ G δ₀).card : ℝ) * ((1 : ℝ) / (2 ^ 48 * (Nat.log 2 q + 1 : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_right h_card_ge (by positivity)
    have h_q_lt_pow : (q : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 q + 1) := by
      have h1 : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by decide) q
      exact_mod_cast le_of_lt h1
    have h_log_q : Real.log (q : ℝ) ≤ (Nat.log 2 q + 1 : ℝ) := by
      have hq_pos_r : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
      have h_log2_le_one : Real.log 2 ≤ 1 := by
        have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have h_cast_L : ((Nat.log 2 q + 1 : ℕ) : ℝ) = (Nat.log 2 q : ℝ) + 1 := by push_cast; ring
      calc Real.log (q : ℝ) ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 q + 1)) :=
            Real.log_le_log hq_pos_r h_q_lt_pow
        _ = ((Nat.log 2 q + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (Nat.log 2 q + 1)
        _ = (Nat.log 2 q + 1 : ℝ) * Real.log 2 := by rw [h_cast_L]
        _ ≤ (Nat.log 2 q + 1 : ℝ) * 1 := mul_le_mul_of_nonneg_left h_log2_le_one (by positivity)
        _ = (Nat.log 2 q + 1 : ℝ) := mul_one _
    linarith

  let V_M : ℕ → Finset ℕ := fun q =>
    if hq : q ∈ Q then Classical.choose (h_V_act_ex q hq) else ∅

  refine ⟨V_M, ?_, ?_, ?_⟩
  · intro q
    dsimp [V_M]
    split_ifs with hq
    · have h_spec := Classical.choose_spec (h_V_act_ex q hq)
      refine ⟨Finset.Subset.trans h_spec.1 (Finset.Subset.trans (hU_M_props q hq).1 (hC_sub q hq)), h_spec.2.1⟩
    · exact ⟨Finset.empty_subset _, by positivity⟩
  · intro q₁ hq₁_Ioc q₂ hq₂_Ioc j₁ hj₁ j₂ hj₂ hne
    have hq₁ : q₁ ∈ Q := by
      by_contra h_not
      simp [V_M, h_not] at hj₁
    have hq₂ : q₂ ∈ Q := by
      by_contra h_not
      simp [V_M, h_not] at hj₂
    have hj₁_U : j₁ ∈ U_M q₁ := by
      dsimp [V_M] at hj₁
      rw [dif_pos hq₁] at hj₁
      exact (Classical.choose_spec (h_V_act_ex q₁ hq₁)).1 hj₁
    have hj₂_U : j₂ ∈ U_M q₂ := by
      dsimp [V_M] at hj₂
      rw [dif_pos hq₂] at hj₂
      exact (Classical.choose_spec (h_V_act_ex q₂ hq₂)).1 hj₂
    have hj₁_lt : j₁ < m_res q₁ := Finset.mem_range.mp (hC_sub q₁ hq₁ ((hU_M_props q₁ hq₁).1 hj₁_U))
    have hj₂_lt : j₂ < m_res q₂ := Finset.mem_range.mp (hC_sub q₂ hq₂ ((hU_M_props q₂ hq₂).1 hj₂_U))
    have hb₁ := (h_bounds q₁ (hQ_gt_B q₁ hq₁) j₁ hj₁_lt).2.1
    have hb₂ := (h_bounds q₂ (hQ_gt_B q₂ hq₂) j₂ hj₂_lt).2.1
    have h_sep_a := hU_M_sep q₁ hq₁ q₂ hq₂ j₁ hj₁_U j₂ hj₂_U hne
    dsimp [a] at h_sep_a
    omega
  · intro q hq_Ioc δ h_dvd1 h_dvd2
    have hq_not_dvd : ¬ (((Finset.Icc 1 q).lcm id) / 1189 ∣ ((Finset.Icc 1 (q - 1)).lcm id) / 1189) := by
      intro h_dvd_lcm
      have h_dvd_int : ((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣
          ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) := Int.ofNat_dvd.mpr h_dvd_lcm
      exact h_dvd2 (Int.dvd_trans h_dvd_int h_dvd1)
    have hq : q ∈ Q := Finset.mem_filter.mpr ⟨hq_Ioc, hq_not_dvd⟩
    dsimp [V_M]
    rw [dif_pos hq]
    exact (Classical.choose_spec (h_V_act_ex q hq)).2.2 δ h_dvd1 h_dvd2

theorem coherent_slice_enumeration_and_reserve_compilation (B : ℕ) (m_res : ℕ → ℕ) (I_res : ℕ → ℕ → ℕ × ℕ)
    (hB : 2 ^ 128 ≤ B)
    (h_bounds : ∀ q > B, ∀ j < m_res q,
      q ^ 2 / (2048 * (Nat.log 2 q + 1)) ≤ (I_res q j).1 ∧
      (I_res q j).2 = (I_res q j).1 + 1 ∧
      (I_res q j).2 ≤ q ^ 2 / 2 ∧
      w_Icc (I_res q j).1 (I_res q j).2 ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2)
    (h_lcm : ∀ q > B, ∀ j < m_res q,
      ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc (I_res q j).1 (I_res q j).2).den = 1)
    (V_inf : ℕ → Finset ℕ)
    (hV_sub : ∀ q : ℕ, V_inf q ⊆ Finset.range (m_res q) ∧ (V_inf q).card ≤ 2 ^ 55 * (Nat.log 2 q + 1) ^ 3)
    (hV_sep : ∀ q₁ > B, ∀ q₂ > B, ∀ j₁ ∈ V_inf q₁, ∀ j₂ ∈ V_inf q₂,
      (q₁ ≠ q₂ ∨ j₁ ≠ j₂) →
      (I_res q₁ j₁).2 + 1 < (I_res q₂ j₂).1 ∨ (I_res q₂ j₂).2 + 1 < (I_res q₁ j₁).1)
    (hV_energy : ∀ q > B, ∀ δ : ℤ,
      ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
      ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
      16 * Real.log (q : ℝ) ≤
        ∑ j ∈ V_inf q,
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) :
    ∃ (l_dig : ℕ → ℕ) (I_dig : ℕ → ℕ × ℕ),
      (∀ k : ℕ, 495 ≤ (I_dig k).1 ∧ (I_dig k).1 < (I_dig k).2 ∧ (I_dig k).2 ≤ (I_dig k).1 + 2) ∧
      (∀ k m : ℕ, k ≠ m → (I_dig k).2 + 1 < (I_dig m).1 ∨ (I_dig m).2 + 1 < (I_dig k).1) ∧
      (1 ≤ l_dig B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_dig Y₁ ≤ l_dig Y₂) ∧
      (∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_dig k).1 (I_dig k).2 ≤ 1 / 237800) ∧
      (∀ Y ≥ B, l_dig Y ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
        ∀ i : Fin (l_dig Y), (I_dig i.1).2 ≤ Y ^ 2 / 2 ∧
          ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_dig i.1).1 (I_dig i.1).2).den = 1) ∧
      (∀ q : ℕ, B < q → ∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        16 * Real.log (q : ℝ) ≤
          ∑ k ∈ (Finset.range (l_dig q)) \ (Finset.range (l_dig (q - 1))),
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_dig k).1 (I_dig k).2 : ℝ)))) ^ 2) :=
by
  classical
  let F_pot : ℕ → ℚ := fun q =>
    (2 ^ 67 : ℚ) * (((Nat.log 2 q + 1 : ℕ) : ℚ) ^ 4 / (q : ℚ) +
      2 * ((Nat.log 2 q + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ (Nat.log 2 q) : ℕ) : ℚ))

  have h_s3 : ∀ Y ≥ B,
      w_Icc 1000000 1000001 + ∑ q ∈ Finset.Ioc B Y, ∑ j ∈ V_inf q, w_Icc (I_res q j).1 (I_res q j).2 ≤ 1 / 237800 := by
    have hw_base : w_Icc 1000000 1000001 ≤ 1 / 475600 := by
      have hIcc : Finset.Icc 1000000 1000001 = ({1000000, 1000001} : Finset ℕ) := rfl
      simp only [w_Icc, hIcc]
      norm_num
    have h_step_pot : ∀ q > B,
        ((2 ^ 67 : ℚ) * ((Nat.log 2 q + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) ^ 2 ≤ F_pot (q - 1) - F_pot q := by
      intro q hq
      set L := Nat.log 2 q
      have hq_ge : 2 ^ 128 < q := lt_of_le_of_lt hB hq
      have hL_ge : 128 ≤ L := by
        have h1 : Nat.log 2 (2 ^ 128) ≤ Nat.log 2 q := Nat.log_mono_right (le_of_lt hq_ge)
        rwa [Nat.log_pow (by decide : 1 < 2)] at h1
      have h2L_le : 2 ^ L ≤ q := Nat.pow_log_le_self 2 (by omega)
      have hq_lt_2L1 : q < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q
      have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
      have hq1_pos : (0 : ℚ) < ((q - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < q - 1)
      have hq1_eq : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      by_cases h_pow : 2 ^ L < q
      · have h_log_prev : Nat.log 2 (q - 1) = L := by
          rw [Nat.log_eq_iff (Or.inl (by omega))]
          exact ⟨by omega, by omega⟩
        dsimp [F_pot]
        rw [h_log_prev]
        have h_diff : (2 ^ 67 : ℚ) * (((L + 1 : ℕ) : ℚ) ^ 4 / ((q - 1 : ℕ) : ℚ) + 2 * ((L + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ L : ℕ) : ℚ)) -
            (2 ^ 67 : ℚ) * (((L + 1 : ℕ) : ℚ) ^ 4 / (q : ℚ) + 2 * ((L + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ L : ℕ) : ℚ)) =
            (2 ^ 67 : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 4 * (1 / ((q - 1 : ℕ) : ℚ) - 1 / (q : ℚ)) := by ring
        rw [h_diff]
        have h_frac : 1 / (q : ℚ) ^ 2 ≤ 1 / ((q - 1 : ℕ) : ℚ) - 1 / (q : ℚ) := by
          rw [hq1_eq, div_sub_div _ _ (by linarith) (by linarith)]
          rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
          linarith
        calc ((2 ^ 67 : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) ^ 2
            = (2 ^ 67 : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 4 * (1 / (q : ℚ) ^ 2) := by ring
          _ ≤ (2 ^ 67 : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 4 * (1 / ((q - 1 : ℕ) : ℚ) - 1 / (q : ℚ)) :=
              mul_le_mul_of_nonneg_left h_frac (by positivity)
      · have hq_eq : q = 2 ^ L := by omega
        have h2L_split : 2 ^ L = 2 * 2 ^ (L - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ L), Nat.pow_succ']
        have h_log_prev : Nat.log 2 (q - 1) = L - 1 := by
          rw [Nat.log_eq_iff (Or.inl (by omega))]
          have : L - 1 + 1 = L := by omega
          rw [this]
          omega
        have hL_sub_add : L - 1 + 1 = L := by omega
        have h_pow_prev : ((2 ^ (L - 1) : ℕ) : ℚ) = (q : ℚ) / 2 := by
          have : (q : ℚ) = 2 * ((2 ^ (L - 1) : ℕ) : ℚ) := by
            exact_mod_cast hq_eq.trans h2L_split
          linarith
        have h_pow_cur : ((2 ^ L : ℕ) : ℚ) = (q : ℚ) := by exact_mod_cast hq_eq.symm
        dsimp [F_pot]
        rw [h_log_prev, hL_sub_add, h_pow_prev, h_pow_cur]
        have h_q1_inv : (L : ℚ) ^ 4 / (q : ℚ) ≤ (L : ℚ) ^ 4 / ((q - 1 : ℕ) : ℚ) := by
          apply div_le_div_of_nonneg_left (by positivity) hq1_pos
          rw [hq1_eq]
          linarith
        have h_poly : ((L + 1 : ℕ) : ℚ) ^ 4 ≤ 5 * (L : ℚ) ^ 4 - 3 * ((L + 1 : ℕ) : ℚ) ^ 4 := by
          push_cast
          have hL_q : (128 : ℚ) ≤ (L : ℚ) := by exact_mod_cast hL_ge
          have h1 : 0 ≤ ((L : ℚ) - 17) * (L : ℚ) ^ 3 := mul_nonneg (by linarith) (by positivity)
          have h2 : 0 ≤ ((L : ℚ) - 25) * (L : ℚ) ^ 2 := mul_nonneg (by linarith) (by positivity)
          have h3 : 0 ≤ ((L : ℚ) - 17) * (L : ℚ) := mul_nonneg (by linarith) (by positivity)
          have h_id_poly : 5 * (L : ℚ) ^ 4 - 4 * ((L : ℚ) + 1) ^ 4 =
              ((L : ℚ) - 17) * (L : ℚ) ^ 3 + ((L : ℚ) - 25) * (L : ℚ) ^ 2 + ((L : ℚ) - 17) * (L : ℚ) + ((L : ℚ) - 4) := by ring
          linarith
        have h_step1 : ((2 ^ 67 : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) ≤
            (2 ^ 67 : ℚ) * ((L : ℚ) ^ 4 / (q : ℚ) + 2 * (L : ℚ) ^ 4 / ((q : ℚ) / 2)) -
            (2 ^ 67 : ℚ) * (((L + 1 : ℕ) : ℚ) ^ 4 / (q : ℚ) + 2 * ((L + 1 : ℕ) : ℚ) ^ 4 / (q : ℚ)) := by
          have h_id : (2 ^ 67 : ℚ) * ((L : ℚ) ^ 4 / (q : ℚ) + 2 * (L : ℚ) ^ 4 / ((q : ℚ) / 2)) -
              (2 ^ 67 : ℚ) * (((L + 1 : ℕ) : ℚ) ^ 4 / (q : ℚ) + 2 * ((L + 1 : ℕ) : ℚ) ^ 4 / (q : ℚ)) =
              (2 ^ 67 : ℚ) * (5 * (L : ℚ) ^ 4 - 3 * ((L + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) := by ring
          rw [h_id]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h_poly (by positivity)) (le_of_lt hq_pos)
        have h_step0 : ((2 ^ 67 : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) ^ 2 ≤
            ((2 ^ 67 : ℚ) * ((L + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) := by
          apply div_le_div_of_nonneg_left (by positivity) hq_pos
          have : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (by omega : 1 ≤ q)
          nlinarith
        linarith
    have h_FB_bound : F_pot B ≤ 1 / 475600 := by
      dsimp [F_pot]
      set K := Nat.log 2 B
      have hK_ge : 128 ≤ K := by
        have h1 : Nat.log 2 (2 ^ 128) ≤ Nat.log 2 B := Nat.log_mono_right hB
        rwa [Nat.log_pow (by decide : 1 < 2)] at h1
      have h2K_le : 2 ^ K ≤ B := Nat.pow_log_le_self 2 (by omega)
      have h2K_pos : (0 : ℚ) < ((2 ^ K : ℕ) : ℚ) := by positivity
      have hB_pos : (0 : ℚ) < (B : ℚ) := by exact_mod_cast (by omega : 0 < B)
      have h_inv_B : ((K + 1 : ℕ) : ℚ) ^ 4 / (B : ℚ) ≤ ((K + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ K : ℕ) : ℚ) := by
        apply div_le_div_of_nonneg_left (by positivity) h2K_pos
        exact_mod_cast h2K_le
      have h_ind_pow : ∀ d : ℕ, 475600 * (3 * 2 ^ 67 * (128 + d + 1) ^ 4) ≤ 2 ^ (128 + d) := by
        intro d
        induction d with
        | zero => norm_num
        | succ d ih =>
          set m := 128 + d + 1
          have hm : (m + 1) ^ 4 ≤ 2 * m ^ 4 := by
            have h2 : (m + 1) ^ 4 = m ^ 4 + (4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1) := by ring
            have h3 : 4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1 ≤ m ^ 4 := by
              calc 4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1
                  ≤ 4 * m ^ 3 + m * m ^ 2 + m * m ^ 2 + m ^ 3 := by
                    have hm_ge : 6 ≤ m := by omega
                    nlinarith
                _ = 7 * m ^ 3 := by ring
                _ ≤ m * m ^ 3 := Nat.mul_le_mul_right (m ^ 3) (by omega)
                _ = m ^ 4 := by ring
            omega
          calc 475600 * (3 * 2 ^ 67 * (128 + (d + 1) + 1) ^ 4)
              = 475600 * (3 * 2 ^ 67 * (m + 1) ^ 4) := by rfl
            _ ≤ 475600 * (3 * 2 ^ 67 * (2 * m ^ 4)) :=
                Nat.mul_le_mul_left 475600 (Nat.mul_le_mul_left (3 * 2 ^ 67) hm)
            _ = 2 * (475600 * (3 * 2 ^ 67 * m ^ 4)) := by ring
            _ ≤ 2 * 2 ^ (128 + d) := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (128 + (d + 1)) := by rw [← Nat.pow_succ']; rfl
      have h_nat_bound : 475600 * (3 * 2 ^ 67 * (K + 1) ^ 4) ≤ 2 ^ K := by
        have h := h_ind_pow (K - 128)
        rwa [Nat.add_sub_of_le hK_ge] at h
      have h_q_bound : (2 ^ 67 : ℚ) * (3 * ((K + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ K : ℕ) : ℚ)) ≤ 1 / 475600 := by
        rw [mul_div_assoc', div_le_div_iff₀ h2K_pos (by norm_num)]
        have h_q : (475600 : ℚ) * ((3 : ℚ) * (2 ^ 67 : ℚ) * ((K + 1 : ℕ) : ℚ) ^ 4) ≤ ((2 ^ K : ℕ) : ℚ) := by
          exact_mod_cast h_nat_bound
        linarith
      have h_eq3 : 3 * ((K + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ K : ℕ) : ℚ) =
          ((K + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ K : ℕ) : ℚ) + 2 * ((K + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ K : ℕ) : ℚ) := by ring
      have h_sum_b : ((K + 1 : ℕ) : ℚ) ^ 4 / (B : ℚ) + 2 * ((K + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ K : ℕ) : ℚ) ≤
          3 * ((K + 1 : ℕ) : ℚ) ^ 4 / ((2 ^ K : ℕ) : ℚ) := by linarith
      exact le_trans (mul_le_mul_of_nonneg_left h_sum_b (by positivity)) h_q_bound
    intro Y hBY
    have h_slice_le : ∀ q ∈ Finset.Ioc B Y,
        ∑ j ∈ V_inf q, w_Icc (I_res q j).1 (I_res q j).2 ≤ F_pot (q - 1) - F_pot q := by
      intro q hq
      rw [Finset.mem_Ioc] at hq
      have h_term : ∀ j ∈ V_inf q,
          w_Icc (I_res q j).1 (I_res q j).2 ≤ (4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2 := by
        intro j hj
        have hj_lt : j < m_res q := Finset.mem_range.mp ((hV_sub q).1 hj)
        exact (h_bounds q hq.1 j hj_lt).2.2.2
      have h_sum := Finset.sum_le_card_nsmul (V_inf q) (fun j => w_Icc (I_res q j).1 (I_res q j).2)
        ((4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2) h_term
      rw [nsmul_eq_mul] at h_sum
      have h_card : ((V_inf q).card : ℚ) ≤ (2 ^ 55 * (Nat.log 2 q + 1) ^ 3 : ℚ) := by
        exact_mod_cast (hV_sub q).2
      have h_prod : ((V_inf q).card : ℚ) * ((4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2) ≤
          ((2 ^ 67 : ℚ) * ((Nat.log 2 q + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) ^ 2 := by
        calc ((V_inf q).card : ℚ) * ((4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2)
            ≤ (2 ^ 55 * (Nat.log 2 q + 1) ^ 3 : ℚ) * ((4096 * (Nat.log 2 q + 1) : ℚ) / (q : ℚ) ^ 2) :=
              mul_le_mul_of_nonneg_right h_card (by positivity)
          _ = ((2 ^ 67 : ℚ) * ((Nat.log 2 q + 1 : ℕ) : ℚ) ^ 4) / (q : ℚ) ^ 2 := by
              push_cast
              ring
      exact le_trans h_sum (le_trans h_prod (h_step_pot q hq.1))
    have h_sum_tele : ∀ d : ℕ,
        ∑ q ∈ Finset.Ioc B (B + d), (F_pot (q - 1) - F_pot q) = F_pot B - F_pot (B + d) := by
      intro d
      induction d with
      | zero =>
        rw [Nat.add_zero, Finset.Ioc_self, Finset.sum_empty, sub_self]
      | succ d ih =>
        set q := B + (d + 1)
        have h_ins : Finset.Ioc B q = insert q (Finset.Ioc B (B + d)) := by
          ext x
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          omega
        have h_not : q ∉ Finset.Ioc B (B + d) := by
          rw [Finset.mem_Ioc]
          omega
        have hq_prev : q - 1 = B + d := by omega
        rw [h_ins, Finset.sum_insert h_not, ih, hq_prev]
        ring
    have h_FY_nonneg : 0 ≤ F_pot Y := by
      dsimp [F_pot]
      positivity
    have h_sum_le := Finset.sum_le_sum h_slice_le
    have h_tele_Y := h_sum_tele (Y - B)
    rw [Nat.add_sub_of_le hBY] at h_tele_Y
    rw [h_tele_Y] at h_sum_le
    linarith

  have h_s4 :
      (∀ q > B, 1000003 ≤ q ^ 2 / (2048 * (Nat.log 2 q + 1))) ∧
      (∀ Y ≥ B, 1000001 ≤ Y ^ 2 / 2 ∧
        ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc 1000000 1000001).den = 1) ∧
      (∀ Y ≥ B, ∀ q ∈ Finset.Ioc B Y, ∀ a b : ℕ,
        ((((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a b).den = 1 →
        ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc a b).den = 1) ∧
      (∀ Y ≥ B, 1 + ∑ q ∈ Finset.Ioc B Y, (V_inf q).card ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      set L := Nat.log 2 q
      have hq_ge : 2 ^ 128 < q := lt_of_le_of_lt hB hq
      have h2L_le : 2 ^ L ≤ q := Nat.pow_log_le_self 2 (by omega)
      have hL_lt : L < 2 ^ L := Nat.lt_two_pow_self
      have hL1_le_q : L + 1 ≤ q := by omega
      have h_const_le_q : 1000003 * 2048 ≤ q := by omega
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc 1000003 * (2048 * (L + 1))
          = (1000003 * 2048) * (L + 1) := by ring
        _ ≤ q * q := Nat.mul_le_mul h_const_le_q hL1_le_q
        _ = q ^ 2 := (sq q).symm
    · intro Y hBY
      have hY_ge : 2 ^ 128 ≤ Y := le_trans hB hBY
      refine ⟨?_, ?_⟩
      · have : 2000002 ≤ Y * Y := by
          calc 2000002 ≤ 2 ^ 128 * 2 ^ 128 := by norm_num
            _ ≤ Y * Y := Nat.mul_le_mul hY_ge hY_ge
        rw [sq, Nat.le_div_iff_mul_le (by decide)]
        omega
      · set D := (Finset.Icc 1 Y).lcm id
        have h1 : 1000000 ∣ D := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have h2 : 1000001 ∣ D := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        obtain ⟨u, hu⟩ := h1
        obtain ⟨v, hv⟩ := h2
        have hIcc : Finset.Icc 1000000 1000001 = ({1000000, 1000001} : Finset ℕ) := rfl
        have h_eq : (D : ℚ) * w_Icc 1000000 1000001 = ((u + v : ℕ) : ℚ) := by
          simp only [w_Icc, hIcc, Finset.sum_insert (by decide : (1000000 : ℕ) ∉ ({1000001} : Finset ℕ)), Finset.sum_singleton]
          have hu_q : (D : ℚ) = 1000000 * (u : ℚ) := by exact_mod_cast hu
          have hv_q : (D : ℚ) = 1000001 * (v : ℚ) := by exact_mod_cast hv
          push_cast
          calc (D : ℚ) * ((1000000 : ℚ)⁻¹ + (1000001 : ℚ)⁻¹)
              = (D : ℚ) * (1000000 : ℚ)⁻¹ + (D : ℚ) * (1000001 : ℚ)⁻¹ := by ring
            _ = (1000000 * (u : ℚ)) * (1000000 : ℚ)⁻¹ + (1000001 * (v : ℚ)) * (1000001 : ℚ)⁻¹ := by
                rw [← hu_q, ← hv_q]
            _ = (u : ℚ) + (v : ℚ) := by ring
        rw [h_eq, Rat.den_natCast]
    · intro Y hBY q hq a b h_den
      rw [Finset.mem_Ioc] at hq
      have h_sub : Finset.Icc 1 q ⊆ Finset.Icc 1 Y := Finset.Icc_subset_Icc_right hq.2
      have h_dvd : (Finset.Icc 1 q).lcm id ∣ (Finset.Icc 1 Y).lcm id :=
        Finset.lcm_dvd (fun x hx => Finset.dvd_lcm (h_sub hx))
      obtain ⟨c, hc⟩ := h_dvd
      set x : ℚ := (((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * w_Icc a b
      have hx_eq : x = (x.num : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den x, h_den, Nat.cast_one, div_one]
      have h_prod : (((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc a b = (((c : ℤ) * x.num : ℤ) : ℚ) := by
        have hc_q : (((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) = (((Finset.Icc 1 q).lcm id : ℕ) : ℚ) * (c : ℚ) := by
          exact_mod_cast hc
        calc (((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc a b
            = (c : ℚ) * x := by rw [hc_q]; ring
          _ = (c : ℚ) * (x.num : ℚ) := by rw [← hx_eq]
          _ = (((c : ℤ) * x.num : ℤ) : ℚ) := by push_cast; ring
      rw [h_prod, Rat.den_intCast]
    · intro Y hBY
      have hY_pos : 1 ≤ Y := by omega
      have h_term : ∀ q ∈ Finset.Ioc B Y, (V_inf q).card ≤ 2 ^ 55 * (Nat.log 2 Y + 1) ^ 3 := by
        intro q hq
        rw [Finset.mem_Ioc] at hq
        have h_log : Nat.log 2 q ≤ Nat.log 2 Y := Nat.log_mono_right hq.2
        have h_pow : (Nat.log 2 q + 1) ^ 3 ≤ (Nat.log 2 Y + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        exact le_trans (hV_sub q).2 (Nat.mul_le_mul_left (2 ^ 55) h_pow)
      have h_sum := Finset.sum_le_card_nsmul (Finset.Ioc B Y) (fun q => (V_inf q).card) (2 ^ 55 * (Nat.log 2 Y + 1) ^ 3) h_term
      rw [Nat.card_Ioc, smul_eq_mul] at h_sum
      have h_sub_le : Y - B ≤ Y := Nat.sub_le Y B
      have h_sum2 : ∑ q ∈ Finset.Ioc B Y, (V_inf q).card ≤ Y * (2 ^ 55 * (Nat.log 2 Y + 1) ^ 3) :=
        le_trans h_sum (Nat.mul_le_mul_right _ h_sub_le)
      have h_one : 1 ≤ Y * (2 ^ 55 * (Nat.log 2 Y + 1) ^ 3) :=
        Nat.mul_pos hY_pos (Nat.mul_pos (by positivity) (by positivity))
      calc 1 + ∑ q ∈ Finset.Ioc B Y, (V_inf q).card
          ≤ Y * (2 ^ 55 * (Nat.log 2 Y + 1) ^ 3) + Y * (2 ^ 55 * (Nat.log 2 Y + 1) ^ 3) := add_le_add h_one h_sum2
        _ = 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 := by ring

  have h_unb : ∀ k : ℕ, ∃ Y : ℕ, B ≤ Y ∧ k < 1 + ∑ q ∈ Finset.Ioc B Y, (V_inf q).card := by
    have h_prime_nonempty : ∀ p : ℕ, B < p → Nat.Prime p → 1 ≤ (V_inf p).card := by
      intro p hpB hp
      have h_cop_lcm : ∀ n < p, Nat.Coprime p ((Finset.Icc 1 n).lcm id) := by
        intro n
        induction n with
        | zero =>
          intro _
          have : Finset.Icc 1 0 = ∅ := rfl
          rw [this, Finset.lcm_empty]
          exact Nat.coprime_one_right p
        | succ n ih =>
          intro hnp
          have h_ins : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
            ext x
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          rw [h_ins, Finset.lcm_insert]
          have h_cop1 : Nat.Coprime p (n + 1) := by
            rw [hp.coprime_iff_not_dvd]
            intro h_dvd
            have := Nat.le_of_dvd (by omega) h_dvd
            omega
          have h_cop2 : Nat.Coprime p ((Finset.Icc 1 n).lcm id) := ih (by omega)
          exact (h_cop1.mul_right h_cop2).coprime_dvd_right (Nat.lcm_dvd_mul (n + 1) ((Finset.Icc 1 n).lcm id))
      set D_prev := (Finset.Icc 1 (p - 1)).lcm id
      set D_cur := (Finset.Icc 1 p).lcm id
      have h29 : 29 ∣ D_prev := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have h41 : 41 ∣ D_prev := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have h1189_prev : 1189 ∣ D_prev := (by decide : Nat.Coprime 29 41).mul_dvd_of_dvd_of_dvd h29 h41
      have h29_cur : 29 ∣ D_cur := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have h41_cur : 41 ∣ D_cur := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have h1189_cur : 1189 ∣ D_cur := (by decide : Nat.Coprime 29 41).mul_dvd_of_dvd_of_dvd h29_cur h41_cur
      set δ : ℤ := ((D_prev / 1189 : ℕ) : ℤ)
      have h_not_dvd : ¬ (((D_cur / 1189 : ℕ) : ℤ) ∣ δ) := by
        intro h_dvd_z
        have h_dvd_nat : D_cur / 1189 ∣ D_prev / 1189 := Int.ofNat_dvd.mp h_dvd_z
        have h_mul_dvd : 1189 * (D_cur / 1189) ∣ 1189 * (D_prev / 1189) := Nat.mul_dvd_mul_left 1189 h_dvd_nat
        rw [Nat.mul_div_cancel' h1189_cur, Nat.mul_div_cancel' h1189_prev] at h_mul_dvd
        have hp_dvd_cur : p ∣ D_cur := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, le_refl p⟩)
        have hp_dvd_prev : p ∣ D_prev := dvd_trans hp_dvd_cur h_mul_dvd
        have h_cop : Nat.Coprime p D_prev := h_cop_lcm (p - 1) (by omega)
        have hp_dvd_one : p ∣ 1 := by
          rw [← h_cop.gcd_eq_one]
          exact Nat.dvd_gcd (dvd_refl p) hp_dvd_prev
        have := Nat.le_of_dvd (by decide) hp_dvd_one
        omega
      have h_en := hV_energy p hpB δ (dvd_refl δ) h_not_dvd
      have h_log_pos : 0 < 16 * Real.log (p : ℝ) := by
        have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
        have := Real.log_pos hp_gt1
        linarith
      by_contra h_empty
      have h_card0 : (V_inf p).card = 0 := by omega
      rw [Finset.card_eq_zero.mp h_card0, Finset.sum_empty] at h_en
      linarith
    intro k
    induction k with
    | zero =>
      refine ⟨B, le_refl B, by omega⟩
    | succ k ih =>
      obtain ⟨Y, hBY, hkY⟩ := ih
      obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (Y + 1)
      refine ⟨p, by omega, ?_⟩
      have hp_card : 1 ≤ (V_inf p).card := h_prime_nonempty p (by omega) hp_prime
      have h_sub : insert p (Finset.Ioc B Y) ⊆ Finset.Ioc B p := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_Ioc] at hx ⊢
        omega
      have hp_not : p ∉ Finset.Ioc B Y := by
        rw [Finset.mem_Ioc]
        omega
      have h_sum_le := Finset.sum_le_sum_of_subset (f := fun q => (V_inf q).card) h_sub
      rw [Finset.sum_insert hp_not] at h_sum_le
      dsimp only at h_sum_le
      omega

  let l_dig : ℕ → ℕ := fun Y => 1 + ∑ q ∈ Finset.Ioc B Y, (V_inf q).card
  have hl_mono : ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_dig Y₁ ≤ l_dig Y₂ := by
    intro Y₁ Y₂ h12
    dsimp [l_dig]
    exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.Ioc_subset_Ioc_right h12)) 1
  have hl_le_B : ∀ Y ≤ B, l_dig Y = 1 := by
    intro Y hY
    dsimp [l_dig]
    have : Finset.Ioc B Y = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    rfl
  have hl_step : ∀ q > B, l_dig q = l_dig (q - 1) + (V_inf q).card := by
    intro q hq
    dsimp [l_dig]
    have h_ins : Finset.Ioc B q = insert q (Finset.Ioc B (q - 1)) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have h_not : q ∉ Finset.Ioc B (q - 1) := by
      rw [Finset.mem_Ioc]
      omega
    rw [h_ins, Finset.sum_insert h_not]
    omega
  have h_ex : ∀ k : ℕ, ∃ Y : ℕ, k < l_dig Y := fun k => ⟨(h_unb k).choose, (h_unb k).choose_spec.2⟩
  let q_of : ℕ → ℕ := fun k => Nat.find (h_ex k)
  let elem_of : ℕ → ℕ → ℕ := fun q r =>
    if hr : r < (V_inf q).card then ((V_inf q).equivFin.symm ⟨r, hr⟩).1 else 0
  let j_of : ℕ → ℕ := fun k => elem_of (q_of k) (k - l_dig (q_of k - 1))
  let I_dig : ℕ → ℕ × ℕ := fun k => if k = 0 then (1000000, 1000001) else I_res (q_of k) (j_of k)
  have hI0 : I_dig 0 = (1000000, 1000001) := rfl
  have hq_spec : ∀ k : ℕ, k < l_dig (q_of k) := fun k => Nat.find_spec (h_ex k)
  have hq_min : ∀ k Y : ℕ, k < l_dig Y → q_of k ≤ Y := fun k Y h => Nat.find_min' (h_ex k) h
  have hq_gt_B : ∀ k ≥ 1, B < q_of k := by
    intro k hk
    by_contra h_le
    have h1 := hl_le_B (q_of k) (by omega)
    have h2 := hq_spec k
    omega
  have hq_lower : ∀ k ≥ 1, l_dig (q_of k - 1) ≤ k := by
    intro k hk
    have hqB := hq_gt_B k hk
    have h_lt : q_of k - 1 < q_of k := by omega
    exact not_lt.mp (Nat.find_min (h_ex k) h_lt)
  have hr_lt : ∀ k ≥ 1, k - l_dig (q_of k - 1) < (V_inf (q_of k)).card := by
    intro k hk
    have h1 := hq_spec k
    have h2 := hq_lower k hk
    have h3 := hl_step (q_of k) (hq_gt_B k hk)
    omega
  have hq_eq_of_slice : ∀ q > B, ∀ k : ℕ, l_dig (q - 1) ≤ k → k < l_dig q → q_of k = q := by
    intro q hq k hk1 hk2
    have hle : q_of k ≤ q := hq_min k q hk2
    by_contra hne
    have hlt : q_of k ≤ q - 1 := by omega
    have h_m := hl_mono (q_of k) (q - 1) hlt
    have h_s := hq_spec k
    omega
  have h_slice_sum : ∀ {M : Type} [AddCommMonoid M] (f : ℕ × ℕ → M) (q : ℕ), B < q →
      ∑ k ∈ (Finset.range (l_dig q)) \ (Finset.range (l_dig (q - 1))), f (I_dig k) =
        ∑ j ∈ V_inf q, f (I_res q j) := by
    intro M _ f q hq
    have h_sdiff : (Finset.range (l_dig q)) \ (Finset.range (l_dig (q - 1))) = Finset.Ico (l_dig (q - 1)) (l_dig q) := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
      omega
    have h_congr : ∀ k ∈ Finset.Ico (l_dig (q - 1)) (l_dig q),
        f (I_dig k) = f (I_res q (elem_of q (k - l_dig (q - 1)))) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hl_pos : 1 ≤ l_dig (q - 1) := by dsimp [l_dig]; omega
      have hk_ne0 : k ≠ 0 := by omega
      have hqk : q_of k = q := hq_eq_of_slice q hq k hk.1 hk.2
      dsimp [I_dig, j_of]
      rw [if_neg hk_ne0, hqk]
    rw [h_sdiff, Finset.sum_congr rfl h_congr, Finset.sum_Ico_eq_sum_range]
    have h_diff_eq : l_dig q - l_dig (q - 1) = (V_inf q).card := by
      have := hl_step q hq
      omega
    rw [h_diff_eq]
    have h_cancel : ∀ x ∈ Finset.range (V_inf q).card,
        f (I_res q (elem_of q (l_dig (q - 1) + x - l_dig (q - 1)))) = f (I_res q (elem_of q x)) := by
      intro x _
      rw [Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl h_cancel, ← Fin.sum_univ_eq_sum_range]
    have h_fin_eq : ∀ i : Fin (V_inf q).card,
        f (I_res q (elem_of q i.1)) = f (I_res q ((V_inf q).equivFin.symm i).1) := by
      intro i
      dsimp [elem_of]
      rw [if_pos i.2]
    rw [Finset.sum_congr rfl (fun i _ => h_fin_eq i)]
    exact (Finset.sum_equiv (V_inf q).equivFin.symm (by simp) (by simp)).trans
      (Finset.sum_attach (V_inf q) (fun j => f (I_res q j)))

  have h_coord : ∀ k ≥ 1, B < q_of k ∧ j_of k ∈ V_inf (q_of k) ∧ I_dig k = I_res (q_of k) (j_of k) ∧
      ∀ Y ≥ B, k < l_dig Y → q_of k ≤ Y := by
    intro k hk
    refine ⟨hq_gt_B k hk, ?_, ?_, fun Y _ hkY => hq_min k Y hkY⟩
    · dsimp [j_of, elem_of]
      rw [dif_pos (hr_lt k hk)]
      exact ((V_inf (q_of k)).equivFin.symm ⟨_, hr_lt k hk⟩).2
    · dsimp [I_dig]
      rw [if_neg (by omega)]

  have h_inj : ∀ k m : ℕ, 1 ≤ k → 1 ≤ m → k ≠ m → q_of k ≠ q_of m ∨ j_of k ≠ j_of m := by
    intro k m hk hm hkm
    by_contra! h_both
    rcases h_both with ⟨hq_eq, hj_eq⟩
    set q := q_of k
    have hrk : k - l_dig (q - 1) < (V_inf q).card := hr_lt k hk
    have hrm : m - l_dig (q - 1) < (V_inf q).card := by
      rw [hq_eq]
      exact hr_lt m hm
    have hj_eq' : elem_of q (k - l_dig (q - 1)) = elem_of q (m - l_dig (q - 1)) := by
      dsimp [j_of] at hj_eq
      rw [← hq_eq] at hj_eq
      exact hj_eq
    dsimp [elem_of] at hj_eq'
    rw [dif_pos hrk, dif_pos hrm] at hj_eq'
    have h_sub_eq := ((V_inf q).equivFin.symm).injective (Subtype.ext hj_eq')
    have h_idx_eq : k - l_dig (q - 1) = m - l_dig (q - 1) := congr_arg Fin.val h_sub_eq
    have h_low_k : l_dig (q - 1) ≤ k := hq_lower k hk
    have h_low_m : l_dig (q - 1) ≤ m := by
      rw [hq_eq]
      exact hq_lower m hm
    omega

  have h_sum_w : ∀ Y ≥ B,
      ∑ k ∈ Finset.range (l_dig Y), w_Icc (I_dig k).1 (I_dig k).2 =
        w_Icc 1000000 1000001 + ∑ q ∈ Finset.Ioc B Y, ∑ j ∈ V_inf q, w_Icc (I_res q j).1 (I_res q j).2 := by
    intro Y hBY
    have h_ind : ∀ d : ℕ,
        ∑ k ∈ Finset.range (l_dig (B + d)), w_Icc (I_dig k).1 (I_dig k).2 =
          w_Icc 1000000 1000001 + ∑ q ∈ Finset.Ioc B (B + d), ∑ j ∈ V_inf q, w_Icc (I_res q j).1 (I_res q j).2 := by
      intro d
      induction d with
      | zero =>
        rw [Nat.add_zero, hl_le_B B (le_refl B), Finset.range_one, Finset.sum_singleton, Finset.Ioc_self, Finset.sum_empty, add_zero]
        rfl
      | succ d ih =>
        set q := B + (d + 1)
        have hqB : B < q := by omega
        have hq_prev : q - 1 = B + d := by omega
        have h_sub_r : Finset.range (l_dig (B + d)) ⊆ Finset.range (l_dig q) :=
          Finset.range_mono (hl_mono (B + d) q (by omega))
        rw [← Finset.sum_sdiff h_sub_r, ih, ← hq_prev]
        have h_sl := h_slice_sum (fun p : ℕ × ℕ => w_Icc p.1 p.2) q hqB
        dsimp only at h_sl
        rw [h_sl, hq_prev]
        have h_ins : Finset.Ioc B q = insert q (Finset.Ioc B (B + d)) := by
          ext x
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          omega
        have h_not : q ∉ Finset.Ioc B (B + d) := by
          rw [Finset.mem_Ioc]
          omega
        rw [h_ins, Finset.sum_insert h_not]
        ring
    have h := h_ind (Y - B)
    rwa [Nat.add_sub_of_le hBY] at h

  refine ⟨l_dig, I_dig, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hI0]
      omega
    · have hk1 : 1 ≤ k := by omega
      obtain ⟨hqB, hj_mem, hIk, _⟩ := h_coord k hk1
      have hj_lt : j_of k < m_res (q_of k) := Finset.mem_range.mp ((hV_sub (q_of k)).1 hj_mem)
      have hb := h_bounds (q_of k) hqB (j_of k) hj_lt
      have h_low := h_s4.1 (q_of k) hqB
      rw [hIk]
      omega
  · intro k m hkm
    rcases eq_or_ne k 0 with rfl | hk0
    · left
      have hm1 : 1 ≤ m := by omega
      obtain ⟨hqB, hj_mem, hIm, _⟩ := h_coord m hm1
      have hj_lt : j_of m < m_res (q_of m) := Finset.mem_range.mp ((hV_sub (q_of m)).1 hj_mem)
      have hb := (h_bounds (q_of m) hqB (j_of m) hj_lt).1
      have h_low := h_s4.1 (q_of m) hqB
      rw [hI0, hIm]
      omega
    · rcases eq_or_ne m 0 with rfl | hm0
      · right
        have hk1 : 1 ≤ k := by omega
        obtain ⟨hqB, hj_mem, hIk, _⟩ := h_coord k hk1
        have hj_lt : j_of k < m_res (q_of k) := Finset.mem_range.mp ((hV_sub (q_of k)).1 hj_mem)
        have hb := (h_bounds (q_of k) hqB (j_of k) hj_lt).1
        have h_low := h_s4.1 (q_of k) hqB
        rw [hI0, hIk]
        omega
      · have hk1 : 1 ≤ k := by omega
        have hm1 : 1 ≤ m := by omega
        obtain ⟨hqkB, hjk_mem, hIk, _⟩ := h_coord k hk1
        obtain ⟨hqmB, hjm_mem, hIm, _⟩ := h_coord m hm1
        rw [hIk, hIm]
        exact hV_sep (q_of k) hqkB (q_of m) hqmB (j_of k) hjk_mem (j_of m) hjm_mem (h_inj k m hk1 hm1 hkm)
  · exact ⟨by dsimp [l_dig]; omega, hl_mono⟩
  · intro n
    obtain ⟨Y, hBY, hnY⟩ := h_unb n
    have h_sub_r : Finset.range n ⊆ Finset.range (l_dig Y) := Finset.range_mono (le_of_lt hnY)
    have h_le_Y : ∑ k ∈ Finset.range n, w_Icc (I_dig k).1 (I_dig k).2 ≤
        ∑ k ∈ Finset.range (l_dig Y), w_Icc (I_dig k).1 (I_dig k).2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg h_sub_r ?_
      intro k _ _
      apply Finset.sum_nonneg
      intro x _
      positivity
    rw [h_sum_w Y hBY] at h_le_Y
    exact le_trans h_le_Y (h_s3 Y hBY)
  · intro Y hBY
    refine ⟨h_s4.2.2.2 Y hBY, fun i => ?_⟩
    rcases eq_or_ne i.1 0 with hi0 | hi_pos
    · rw [hi0, hI0]
      exact h_s4.2.1 Y hBY
    · have hi1 : 1 ≤ i.1 := by omega
      obtain ⟨hqB, hj_mem, hIi, hq_le⟩ := h_coord i.1 hi1
      have hqY : q_of i.1 ≤ Y := hq_le Y hBY i.2
      have hj_lt : j_of i.1 < m_res (q_of i.1) := Finset.mem_range.mp ((hV_sub (q_of i.1)).1 hj_mem)
      have hb2 := (h_bounds (q_of i.1) hqB (j_of i.1) hj_lt).2.2.1
      have h_lcm_i := h_lcm (q_of i.1) hqB (j_of i.1) hj_lt
      rw [hIi]
      refine ⟨?_, ?_⟩
      · have h_sq : (q_of i.1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hqY 2
        exact le_trans hb2 (Nat.div_le_div_right h_sq)
      · exact h_s4.2.2.1 Y hBY (q_of i.1) (Finset.mem_Ioc.mpr ⟨hqB, hqY⟩) _ _ h_lcm_i
  · intro q hq δ h_dvd1 h_dvd2
    have h_sl := h_slice_sum (fun p : ℕ × ℕ => (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc p.1 p.2 : ℝ)))) ^ 2) q hq
    dsimp only at h_sl
    rw [h_sl]
    exact hV_energy q hq δ h_dvd1 h_dvd2

theorem coherent_digit_reserve_existence : ∃ (B : ℕ) (l_dig : ℕ → ℕ) (I_dig : ℕ → ℕ × ℕ),
      1189 ≤ B ∧
      (∀ k : ℕ, 495 ≤ (I_dig k).1 ∧ (I_dig k).1 < (I_dig k).2 ∧ (I_dig k).2 ≤ (I_dig k).1 + 2) ∧
      (∀ k m : ℕ, k ≠ m → (I_dig k).2 + 1 < (I_dig m).1 ∨ (I_dig m).2 + 1 < (I_dig k).1) ∧
      (1 ≤ l_dig B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_dig Y₁ ≤ l_dig Y₂) ∧
      (∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_dig k).1 (I_dig k).2 ≤ 1 / 237800) ∧
      (∀ Y ≥ B, l_dig Y ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
        ∀ i : Fin (l_dig Y), (I_dig i.1).2 ≤ Y ^ 2 / 2 ∧
          ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_dig i.1).1 (I_dig i.1).2).den = 1) ∧
      (∀ q : ℕ, B < q → ∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        16 * Real.log (q : ℝ) ≤
          ∑ k ∈ (Finset.range (l_dig q)) \ (Finset.range (l_dig (q - 1))),
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_dig k).1 (I_dig k).2 : ℝ)))) ^ 2) :=
by
  classical
  obtain ⟨B, m_res, I_res, hB_128, h_bounds, h_sep, h_dist, h_lcm, h_phase⟩ :=
    prime_power_digit_reservoir_existence
  have hB_1189 : 1189 ≤ B := by omega
  have h_thin_all : ∀ M : ℕ, ∃ V_M : ℕ → Finset ℕ,
      (∀ q : ℕ, V_M q ⊆ Finset.range (m_res q) ∧ (V_M q).card ≤ 2 ^ 55 * (Nat.log 2 q + 1) ^ 3) ∧
      (∀ q₁ ∈ Finset.Ioc B M, ∀ q₂ ∈ Finset.Ioc B M, ∀ j₁ ∈ V_M q₁, ∀ j₂ ∈ V_M q₂,
        (q₁ ≠ q₂ ∨ j₁ ≠ j₂) →
        (I_res q₁ j₁).2 + 1 < (I_res q₂ j₂).1 ∨ (I_res q₂ j₂).2 + 1 < (I_res q₁ j₁).1) ∧
      (∀ q ∈ Finset.Ioc B M, ∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        16 * Real.log (q : ℝ) ≤
          ∑ j ∈ V_M q,
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) :=
    fun M => finite_horizon_simultaneous_thinning_existence B m_res I_res hB_128 h_bounds h_sep h_dist h_lcm h_phase M
  let V_hor : ℕ → ℕ → Finset ℕ := fun M => Classical.choose (h_thin_all M)
  have hV_hor : ∀ M : ℕ,
      (∀ q : ℕ, V_hor M q ⊆ Finset.range (m_res q) ∧ (V_hor M q).card ≤ 2 ^ 55 * (Nat.log 2 q + 1) ^ 3) ∧
      (∀ q₁ ∈ Finset.Ioc B M, ∀ q₂ ∈ Finset.Ioc B M, ∀ j₁ ∈ V_hor M q₁, ∀ j₂ ∈ V_hor M q₂,
        (q₁ ≠ q₂ ∨ j₁ ≠ j₂) →
        (I_res q₁ j₁).2 + 1 < (I_res q₂ j₂).1 ∨ (I_res q₂ j₂).2 + 1 < (I_res q₁ j₁).1) ∧
      (∀ q ∈ Finset.Ioc B M, ∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        16 * Real.log (q : ℝ) ≤
          ∑ j ∈ V_hor M q,
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2) :=
    fun M => Classical.choose_spec (h_thin_all M)

  
  have h_konig_step : ∀ (m : ℕ) (f : ℕ → Finset ℕ), (∀ M, f M ⊆ Finset.range m) →
      ∀ (S : Set ℕ), S.Infinite →
        ∃ (A : Finset ℕ), A ⊆ Finset.range m ∧ ({M ∈ S | f M = A} : Set ℕ).Infinite := by
    intro m f hf S hS
    haveI : Infinite S := hS.to_subtype
    let g : S → ↥(Finset.powerset (Finset.range m)) :=
      fun x => ⟨f x.1, Finset.mem_powerset.mpr (hf x.1)⟩
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
    refine ⟨y.1, Finset.mem_powerset.mp y.2, ?_⟩
    have h_inf : (Subtype.val '' (g ⁻¹' {y})).Infinite :=
      Set.Infinite.image (fun _ _ _ _ h => Subtype.ext h) (Set.infinite_coe_iff.mp hy)
    refine h_inf.mono ?_
    rintro M ⟨⟨x, hxS⟩, hx_mem, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff] at hx_mem
    exact ⟨hxS, hx_mem⟩

  have h_exists_ge : ∀ (S : Set ℕ), S.Infinite → ∀ (K : ℕ), ∃ M ∈ S, K ≤ M := by
    intro S hS K
    have h_not_sub : ¬ (S ⊆ ↑(Finset.range K)) := by
      intro h_sub
      exact hS ((Finset.finite_toSet (Finset.range K)).subset h_sub)
    obtain ⟨M, hMS, hM_not⟩ := Set.not_subset.mp h_not_sub
    rw [Finset.mem_coe, Finset.mem_range, not_lt] at hM_not
    exact ⟨M, hMS, hM_not⟩

  let S_seq : ℕ → {S : Set ℕ // S.Infinite} :=
    Nat.rec ⟨Set.univ, Set.infinite_univ⟩ (fun q Sq =>
      let h_ex := h_konig_step (m_res q) (fun M => V_hor M q) (fun M => ((hV_hor M).1 q).1) Sq.1 Sq.2
      ⟨{M ∈ Sq.1 | V_hor M q = Classical.choose h_ex}, (Classical.choose_spec h_ex).2⟩)
  let V_inf : ℕ → Finset ℕ := fun q =>
    Classical.choose (h_konig_step (m_res q) (fun M => V_hor M q) (fun M => ((hV_hor M).1 q).1) (S_seq q).1 (S_seq q).2)
  have hS_step : ∀ q : ℕ, (S_seq (q + 1)).1 = {M ∈ (S_seq q).1 | V_hor M q = V_inf q} := fun _ => rfl
  have hS_mono_add : ∀ a d : ℕ, (S_seq (a + d)).1 ⊆ (S_seq a).1 := by
    intro a d
    induction d with
    | zero => exact Set.Subset.rfl
    | succ d ih =>
      refine Set.Subset.trans ?_ ih
      rw [Nat.add_succ, hS_step (a + d)]
      intro M hM
      exact hM.1
  have hS_mono : ∀ a b : ℕ, a ≤ b → (S_seq b).1 ⊆ (S_seq a).1 := by
    intro a b hab
    have h := hS_mono_add a (b - a)
    rwa [Nat.add_sub_of_le hab] at h
  have h_agree : ∀ K : ℕ, ∃ M : ℕ, K ≤ M ∧ ∀ q ≤ K, V_inf q = V_hor M q := by
    intro K
    obtain ⟨M, hMS, hKM⟩ := h_exists_ge (S_seq (K + 1)).1 (S_seq (K + 1)).2 K
    refine ⟨M, hKM, fun q hq => ?_⟩
    have hM_q : M ∈ (S_seq (q + 1)).1 := hS_mono (q + 1) (K + 1) (by omega) hMS
    rw [hS_step q] at hM_q
    exact hM_q.2.symm

  have hV_sub : ∀ q : ℕ, V_inf q ⊆ Finset.range (m_res q) ∧ (V_inf q).card ≤ 2 ^ 55 * (Nat.log 2 q + 1) ^ 3 := by
    intro q
    obtain ⟨M, _, hM_eq⟩ := h_agree q
    rw [hM_eq q (le_refl q)]
    exact (hV_hor M).1 q

  have hV_sep : ∀ q₁ > B, ∀ q₂ > B, ∀ j₁ ∈ V_inf q₁, ∀ j₂ ∈ V_inf q₂,
      (q₁ ≠ q₂ ∨ j₁ ≠ j₂) →
      (I_res q₁ j₁).2 + 1 < (I_res q₂ j₂).1 ∨ (I_res q₂ j₂).2 + 1 < (I_res q₁ j₁).1 := by
    intro q₁ hq₁ q₂ hq₂ j₁ hj₁ j₂ hj₂ h_ne
    obtain ⟨M, hM_ge, hM_eq⟩ := h_agree (max q₁ q₂)
    have hq₁_le : q₁ ≤ max q₁ q₂ := le_max_left q₁ q₂
    have hq₂_le : q₂ ≤ max q₁ q₂ := le_max_right q₁ q₂
    rw [hM_eq q₁ hq₁_le] at hj₁
    rw [hM_eq q₂ hq₂_le] at hj₂
    refine (hV_hor M).2.1 q₁ ?_ q₂ ?_ j₁ hj₁ j₂ hj₂ h_ne
    · exact Finset.mem_Ioc.mpr ⟨hq₁, le_trans hq₁_le hM_ge⟩
    · exact Finset.mem_Ioc.mpr ⟨hq₂, le_trans hq₂_le hM_ge⟩

  have hV_energy : ∀ q > B, ∀ δ : ℤ,
      ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
      ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
      16 * Real.log (q : ℝ) ≤
        ∑ j ∈ V_inf q,
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_res q j).1 (I_res q j).2 : ℝ)))) ^ 2 := by
    intro q hq δ h_dvd1 h_dvd2
    obtain ⟨M, hM_ge, hM_eq⟩ := h_agree q
    rw [hM_eq q (le_refl q)]
    exact (hV_hor M).2.2 q (Finset.mem_Ioc.mpr ⟨hq, hM_ge⟩) δ h_dvd1 h_dvd2

  obtain ⟨l_dig, I_dig, h_dig_bounds, h_dig_sep, h_dig_mono, h_dig_mass, h_dig_scale, h_dig_energy⟩ :=
    coherent_slice_enumeration_and_reserve_compilation B m_res I_res hB_128 h_bounds h_lcm V_inf hV_sub hV_sep hV_energy
  exact ⟨B, l_dig, I_dig, hB_1189, h_dig_bounds, h_dig_sep, h_dig_mono, h_dig_mass, h_dig_scale, h_dig_energy⟩

theorem universal_lacunary_gadget_sequence_existence (B : ℕ) (hB : 1189 ≤ B) :
    ∃ (J : ℕ → ℕ × ℕ) (p_idx : ℕ → ℕ → ℕ),
      (∀ r : ℕ, 495 ≤ (J r).1 ∧ (J r).1 < (J r).2 ∧ (J r).2 ≤ (J r).1 + 2) ∧
      (∀ r₁ r₂ : ℕ, r₁ ≠ r₂ → (J r₁).2 + 1 < (J r₂).1 ∨ (J r₂).2 + 1 < (J r₁).1) ∧
      (∀ r : ℕ, (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) ≤ (J r).1) ∧
      (∀ n : ℕ, ∑ r ∈ Finset.range n, w_Icc (J r).1 (J r).2 ≤ 1 / 237800) ∧
      (∀ m₁ j₁ m₂ j₂ : ℕ, p_idx m₁ j₁ = p_idx m₂ j₂ → m₁ = m₂ ∧ j₁ = j₂) ∧
      (∀ m j : ℕ,
        let p := p_idx m j
        let m_val := (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))
        (J (3 * p)).2 ≤ 7135 * m_val ∧
        (J (3 * p + 1)).2 ≤ 7135 * m_val ∧
        (J (3 * p + 2)).2 ≤ 7135 * m_val ∧
        2 * (1189 * w_Icc (J (3 * p)).1 (J (3 * p)).2) +
          3 * (1189 * w_Icc (J (3 * p + 1)).1 (J (3 * p + 1)).2) -
          6 * (1189 * w_Icc (J (3 * p + 2)).1 (J (3 * p + 2)).2) = (m_val : ℚ)⁻¹) :=
by
  have w_Icc_pair : ∀ (a : ℕ), w_Icc a (a + 1) = (a : ℚ)⁻¹ + ((a + 1 : ℕ) : ℚ)⁻¹ := by
    intro a
    unfold w_Icc
    have h : Finset.Icc a (a + 1) = {a, a + 1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [h, Finset.sum_pair (by omega)]
  have w_Icc_triple : ∀ (a : ℕ),
      w_Icc a (a + 2) = (a : ℚ)⁻¹ + ((a + 1 : ℕ) : ℚ)⁻¹ + ((a + 2 : ℕ) : ℚ)⁻¹ := by
    intro a
    unfold w_Icc
    have h : Finset.Icc a (a + 2) = insert a {a + 1, a + 2} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [h, Finset.sum_insert (by simp), Finset.sum_pair (by omega), add_assoc]
  have h_ident : ∀ (m_val s : ℕ), 0 < m_val → s = 1189 * m_val →
      2 * (1189 * w_Icc (2 * s) (2 * s + 1)) +
        3 * (1189 * w_Icc (3 * s + 1) (3 * s + 2)) -
        6 * (1189 * w_Icc (6 * s + 2) (6 * s + 4)) = (m_val : ℚ)⁻¹ := by
    intro m_val s hm_pos hs_eq
    have h3 : 3 * s + 2 = (3 * s + 1) + 1 := by omega
    have h6 : 6 * s + 4 = (6 * s + 2) + 2 := by omega
    rw [h3, h6, w_Icc_pair (2 * s), w_Icc_pair (3 * s + 1), w_Icc_triple (6 * s + 2)]
    have hm_q : (m_val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hs_q : (s : ℚ) = 1189 * (m_val : ℚ) := by exact_mod_cast hs_eq
    have h_d1 : ((2 * s : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_d2 : ((2 * s + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_d3 : ((3 * s + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_d4 : ((3 * s + 1 + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_d5 : ((6 * s + 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_d6 : ((6 * s + 2 + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_d7 : ((6 * s + 2 + 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    rw [hs_q]
    field_simp
    ring
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_padic : ∀ (m : ℕ) (k : ℕ), k % 2 = 1 → padicValNat 2 (2 ^ m * k) = m := by
    intro m k hk
    rw [padicValNat.mul (Nat.ne_of_gt (Nat.two_pow_pos m)) (by omega), padicValNat.prime_pow]
    have h_not_dvd : ¬ (2 ∣ k) := by omega
    rw [padicValNat.eq_zero_of_not_dvd h_not_dvd, add_zero]
  have hs_pos : ∀ p : ℕ, 0 < ulgs_s_of B p := by
    intro p
    unfold ulgs_s_of
    have h1 : 0 < 1189 * (2 * padicValNat 2 (p + 1) + 1) := by omega
    exact Nat.mul_pos h1 (Nat.two_pow_pos _)
  have hs_growth : ∀ r : ℕ, (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) ≤ 2 * ulgs_s_of B (r / 3) := by
    intro r
    have h_exp : 20 * (B + 1) + 20 * (r + 1) ≤ 60 * (B + 2) * (r / 3 + 1) := by
      have hr : r + 1 ≤ 3 * (r / 3 + 1) := by omega
      have hB1 : 1 ≤ B + 2 := by omega
      have hr1 : 1 ≤ r / 3 + 1 := by omega
      nlinarith
    have h_pow_B : B + 2 ≤ 2 ^ (10 * (B + 1)) := by
      have h1 : B + 2 < 2 ^ (B + 2) := Nat.lt_two_pow_self
      have h2 : 2 ^ (B + 2) ≤ 2 ^ (10 * (B + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h_sq_B : (B + 2) ^ 2 ≤ 2 ^ (20 * (B + 1)) := by
      calc (B + 2) ^ 2 ≤ (2 ^ (10 * (B + 1))) ^ 2 := Nat.pow_le_pow_left h_pow_B 2
        _ = 2 ^ (10 * (B + 1) * 2) := (Nat.pow_mul 2 (10 * (B + 1)) 2).symm
        _ = 2 ^ (20 * (B + 1)) := by congr 1; ring
    calc (B + 2) ^ 2 * 2 ^ (20 * (r + 1))
        ≤ 2 ^ (20 * (B + 1)) * 2 ^ (20 * (r + 1)) := Nat.mul_le_mul_right _ h_sq_B
      _ = 2 ^ (20 * (B + 1) + 20 * (r + 1)) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ (60 * (B + 2) * (r / 3 + 1)) := Nat.pow_le_pow_right (by decide) h_exp
      _ ≤ 2 * (1189 * (2 * padicValNat 2 (r / 3 + 1) + 1)) * 2 ^ (60 * (B + 2) * (r / 3 + 1)) :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ = 2 * ulgs_s_of B (r / 3) := by unfold ulgs_s_of; rw [Nat.mul_assoc]
  have hJ_ge_2s : ∀ r : ℕ, 2 * ulgs_s_of B (r / 3) ≤ (ulgs_J B r).1 := by
    intro r
    unfold ulgs_J
    dsimp only
    split_ifs <;> omega
  have hJ_growth : ∀ r : ℕ, (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) ≤ (ulgs_J B r).1 :=
    fun r => le_trans (hs_growth r) (hJ_ge_2s r)
  have hB2_ge : 1000000 ≤ (B + 2) ^ 2 := by nlinarith
  refine ⟨ulgs_J B, ulgs_p_idx, ?_, ?_, hJ_growth, ?_, ?_, ?_⟩
  · intro r
    have hg := hJ_growth r
    have h_ge_495 : 495 ≤ (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) := by
      have h1 : 1 ≤ 2 ^ (20 * (r + 1)) := Nat.one_le_two_pow
      have h2 : 495 ≤ (B + 2) ^ 2 := by omega
      exact le_trans h2 (Nat.le_mul_of_pos_right _ h1)
    have h_sp : 0 < ulgs_s_of B (r / 3) := hs_pos (r / 3)
    refine ⟨le_trans h_ge_495 hg, ?_⟩
    unfold ulgs_J
    dsimp only
    split_ifs <;> omega
  · intro r₁ r₂ hne
    let c_of : ℕ → ℕ := fun u => if u = 0 then 2 else if u = 1 then 3 else 6
    let B_of : ℕ → ℕ := fun r => c_of (r % 3) * ulgs_s_of B (r / 3)
    have hJ_box : ∀ r : ℕ, B_of r ≤ (ulgs_J B r).1 ∧ (ulgs_J B r).2 ≤ B_of r + 4 := by
      intro r
      dsimp [B_of, c_of]
      unfold ulgs_J
      dsimp only
      split_ifs <;> omega
    have hB_dvd : ∀ r : ℕ, 1189 ∣ B_of r := by
      intro r
      dsimp [B_of]
      unfold ulgs_s_of
      refine ⟨c_of (r % 3) * (2 * padicValNat 2 (r / 3 + 1) + 1) * 2 ^ (60 * (B + 2) * (r / 3 + 1)), ?_⟩
      set P := 2 ^ (60 * (B + 2) * (r / 3 + 1))
      set K := 2 * padicValNat 2 (r / 3 + 1) + 1
      ring
    have hB_inj : B_of r₁ ≠ B_of r₂ := by
      intro h_eq
      apply hne
      let e_of : ℕ → ℕ := fun u => if u = 1 then 0 else 1
      let b_of : ℕ → ℕ := fun u => if u = 0 then 1 else 3
      have hB_form : ∀ r : ℕ,
          B_of r = 2 ^ (60 * (B + 2) * (r / 3 + 1) + e_of (r % 3)) *
            (b_of (r % 3) * 1189 * (2 * padicValNat 2 (r / 3 + 1) + 1)) := by
        intro r
        dsimp [B_of]
        unfold ulgs_s_of
        set E := 60 * (B + 2) * (r / 3 + 1)
        set K := 2 * padicValNat 2 (r / 3 + 1) + 1
        have hE_succ : 2 ^ (E + 1) = 2 ^ E * 2 := Nat.pow_succ 2 E
        have hu : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
        rcases hu with h0 | h1 | h2
        · rw [h0]
          change 2 * (1189 * K * 2 ^ E) = 2 ^ (E + 1) * (1 * 1189 * K)
          rw [hE_succ]; set P := 2 ^ E; ring
        · rw [h1]
          change 3 * (1189 * K * 2 ^ E) = 2 ^ E * (3 * 1189 * K)
          set P := 2 ^ E; ring
        · rw [h2]
          change 6 * (1189 * K * 2 ^ E) = 2 ^ (E + 1) * (3 * 1189 * K)
          rw [hE_succ]; set P := 2 ^ E; ring
      have h_odd : ∀ r : ℕ, (b_of (r % 3) * 1189 * (2 * padicValNat 2 (r / 3 + 1) + 1)) % 2 = 1 := by
        intro r
        dsimp [b_of]
        split_ifs <;> omega
      have hv1 : padicValNat 2 (B_of r₁) = 60 * (B + 2) * (r₁ / 3 + 1) + e_of (r₁ % 3) := by
        rw [hB_form r₁, h_padic _ _ (h_odd r₁)]
      have hv2 : padicValNat 2 (B_of r₂) = 60 * (B + 2) * (r₂ / 3 + 1) + e_of (r₂ % 3) := by
        rw [hB_form r₂, h_padic _ _ (h_odd r₂)]
      have hv_eq : 60 * (B + 2) * (r₁ / 3 + 1) + e_of (r₁ % 3) =
          60 * (B + 2) * (r₂ / 3 + 1) + e_of (r₂ % 3) := by
        rw [← hv1, ← hv2, h_eq]
      have he1 : e_of (r₁ % 3) ≤ 1 := by dsimp [e_of]; split_ifs <;> omega
      have he2 : e_of (r₂ % 3) ≤ 1 := by dsimp [e_of]; split_ifs <;> omega
      have hp_eq : r₁ / 3 = r₂ / 3 := by
        by_contra h_ne
        rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
        · have : 60 * (B + 2) * (r₁ / 3 + 1) + 1 < 60 * (B + 2) * (r₂ / 3 + 1) := by nlinarith
          omega
        · have : 60 * (B + 2) * (r₂ / 3 + 1) + 1 < 60 * (B + 2) * (r₁ / 3 + 1) := by nlinarith
          omega
      have h_sp : 0 < ulgs_s_of B (r₂ / 3) := hs_pos (r₂ / 3)
      have hc_eq : c_of (r₁ % 3) = c_of (r₂ % 3) := by
        dsimp [B_of] at h_eq
        rw [hp_eq] at h_eq
        exact Nat.eq_of_mul_eq_mul_right h_sp h_eq
      have hu_eq : r₁ % 3 = r₂ % 3 := by
        dsimp [c_of] at hc_eq
        split_ifs at hc_eq <;> omega
      omega
    obtain ⟨k₁, hk₁⟩ := hB_dvd r₁
    obtain ⟨k₂, hk₂⟩ := hB_dvd r₂
    have hk_ne : k₁ ≠ k₂ := by
      intro h_keq
      apply hB_inj
      rw [hk₁, hk₂, h_keq]
    have h_box1 := hJ_box r₁
    have h_box2 := hJ_box r₂
    omega
  · intro n
    have h_term : ∀ r : ℕ, w_Icc (ulgs_J B r).1 (ulgs_J B r).2 ≤ (3 / 1000000 : ℚ) * (2⁻¹ : ℚ) ^ (r + 1) := by
      intro r
      have h_J1_ge : 1000000 * 2 ^ (r + 1) ≤ (ulgs_J B r).1 := by
        have hg := hJ_growth r
        have h_pow_le : 2 ^ (r + 1) ≤ 2 ^ (20 * (r + 1)) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have h_mul : 1000000 * 2 ^ (r + 1) ≤ (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) :=
          Nat.mul_le_mul hB2_ge h_pow_le
        exact le_trans h_mul hg
      have h_J2_le : (ulgs_J B r).2 ≤ (ulgs_J B r).1 + 2 := by
        unfold ulgs_J; dsimp only; split_ifs <;> omega
      have h_pos_bound : (0 : ℚ) < ((1000000 * 2 ^ (r + 1) : ℕ) : ℚ) := by
        exact_mod_cast Nat.mul_pos (by omega) (Nat.two_pow_pos (r + 1))
      have h_mem_le : ∀ x ∈ Finset.Icc (ulgs_J B r).1 (ulgs_J B r).2,
          (x : ℚ)⁻¹ ≤ ((1000000 * 2 ^ (r + 1) : ℕ) : ℚ)⁻¹ := by
        intro x hx
        rw [Finset.mem_Icc] at hx
        exact inv_anti₀ h_pos_bound (by exact_mod_cast le_trans h_J1_ge hx.1)
      have h_sum_le := Finset.sum_le_card_nsmul (Finset.Icc (ulgs_J B r).1 (ulgs_J B r).2)
        (fun x : ℕ => (x : ℚ)⁻¹) (((1000000 * 2 ^ (r + 1) : ℕ) : ℚ)⁻¹) h_mem_le
      rw [Nat.card_Icc, nsmul_eq_mul] at h_sum_le
      have h_card_le : (((ulgs_J B r).2 + 1 - (ulgs_J B r).1 : ℕ) : ℚ) ≤ 3 := by
        exact_mod_cast (by omega : (ulgs_J B r).2 + 1 - (ulgs_J B r).1 ≤ 3)
      have h_inv_eq : (((1000000 * 2 ^ (r + 1) : ℕ) : ℚ)⁻¹) = (1 / 1000000 : ℚ) * (2⁻¹ : ℚ) ^ (r + 1) := by
        push_cast
        rw [mul_inv, inv_pow]
        ring
      have h_step := le_trans h_sum_le (mul_le_mul_of_nonneg_right h_card_le (le_of_lt (inv_pos.mpr h_pos_bound)))
      rw [h_inv_eq] at h_step
      unfold w_Icc
      linarith
    have h_geom_ind : ∀ m : ℕ,
        ∑ r ∈ Finset.range m, (3 / 1000000 : ℚ) * (2⁻¹ : ℚ) ^ (r + 1) =
          (3 / 1000000 : ℚ) * (1 - (2⁻¹ : ℚ) ^ m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
    have h_sum_le : ∑ r ∈ Finset.range n, w_Icc (ulgs_J B r).1 (ulgs_J B r).2 ≤
        ∑ r ∈ Finset.range n, (3 / 1000000 : ℚ) * (2⁻¹ : ℚ) ^ (r + 1) :=
      Finset.sum_le_sum (fun r _ => h_term r)
    rw [h_geom_ind n] at h_sum_le
    have h_pow_nonneg : (0 : ℚ) ≤ (2⁻¹ : ℚ) ^ n := pow_nonneg (by norm_num) n
    linarith
  · intro m₁ j₁ m₂ j₂ h_eq
    have h_pos1 : 0 < 2 ^ m₁ * (2 * j₁ + 1) := Nat.mul_pos (Nat.two_pow_pos m₁) (by omega)
    have h_pos2 : 0 < 2 ^ m₂ * (2 * j₂ + 1) := Nat.mul_pos (Nat.two_pow_pos m₂) (by omega)
    have h_add1 : 2 ^ m₁ * (2 * j₁ + 1) = 2 ^ m₂ * (2 * j₂ + 1) := by
      unfold ulgs_p_idx at h_eq
      omega
    have hm_eq : m₁ = m₂ := by
      have hv1 := h_padic m₁ (2 * j₁ + 1) (by omega)
      have hv2 := h_padic m₂ (2 * j₂ + 1) (by omega)
      rw [← hv1, ← hv2, h_add1]
    subst hm_eq
    have hj_eq : 2 * j₁ + 1 = 2 * j₂ + 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos m₁) h_add1
    exact ⟨rfl, by omega⟩
  · intro m j
    dsimp only
    set p := ulgs_p_idx m j
    have hp_succ : p + 1 = 2 ^ m * (2 * j + 1) := by
      have : 0 < 2 ^ m * (2 * j + 1) := Nat.mul_pos (Nat.two_pow_pos m) (by omega)
      dsimp [p, ulgs_p_idx]
      omega
    have hm_padic : padicValNat 2 (p + 1) = m := by
      rw [hp_succ]
      exact h_padic m (2 * j + 1) (by omega)
    set m_val := (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))
    have hs_eq : ulgs_s_of B p = 1189 * m_val := by
      unfold ulgs_s_of
      dsimp only [m_val]
      rw [hm_padic, hp_succ, ← Nat.mul_assoc (60 * (B + 2)), ← Nat.mul_assoc 1189]
    have hJ0 : ulgs_J B (3 * p) = (2 * ulgs_s_of B p, 2 * ulgs_s_of B p + 1) := by
      unfold ulgs_J
      have h1 : (3 * p) / 3 = p := by omega
      have h2 : (3 * p) % 3 = 0 := by omega
      rw [h1, h2]; rfl
    have hJ1 : ulgs_J B (3 * p + 1) = (3 * ulgs_s_of B p + 1, 3 * ulgs_s_of B p + 2) := by
      unfold ulgs_J
      have h1 : (3 * p + 1) / 3 = p := by omega
      have h2 : (3 * p + 1) % 3 = 1 := by omega
      rw [h1, h2]; rfl
    have hJ2 : ulgs_J B (3 * p + 2) = (6 * ulgs_s_of B p + 2, 6 * ulgs_s_of B p + 4) := by
      unfold ulgs_J
      have h1 : (3 * p + 2) / 3 = p := by omega
      have h2 : (3 * p + 2) % 3 = 2 := by omega
      rw [h1, h2]; rfl
    rw [hJ0, hJ1, hJ2]
    dsimp only
    have hm_ge_4 : 4 ≤ m_val := by
      dsimp only [m_val]
      have h_exp : 2 ≤ 60 * (B + 2) * 2 ^ m * (2 * j + 1) := by
        have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        have h2 : 1 ≤ 2 * j + 1 := by omega
        have h3 : 2 ≤ 60 * (B + 2) := by omega
        have h4 : 2 ≤ 60 * (B + 2) * 2 ^ m := le_trans h3 (Nat.le_mul_of_pos_right _ h1)
        exact le_trans h4 (Nat.le_mul_of_pos_right _ h2)
      have h_pow : 4 ≤ 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1)) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) h_exp
      have h_odd : 1 ≤ 2 * m + 1 := by omega
      exact le_trans h_pow (Nat.le_mul_of_pos_left _ h_odd)
    refine ⟨by omega, by omega, by omega, ?_⟩
    exact h_ident m_val (ulgs_s_of B p) (by omega) hs_eq

theorem pruned_digit_and_gadget_reserve_merge (B : ℕ) (l_dig : ℕ → ℕ) (I_dig : ℕ → ℕ × ℕ)
    (hB : 1189 ≤ B)
    (h_dig_bounds : ∀ k : ℕ, 495 ≤ (I_dig k).1 ∧ (I_dig k).1 < (I_dig k).2 ∧ (I_dig k).2 ≤ (I_dig k).1 + 2)
    (h_dig_sep : ∀ k m : ℕ, k ≠ m → (I_dig k).2 + 1 < (I_dig m).1 ∨ (I_dig m).2 + 1 < (I_dig k).1)
    (h_dig_mono : 1 ≤ l_dig B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_dig Y₁ ≤ l_dig Y₂)
    (h_dig_mass : ∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_dig k).1 (I_dig k).2 ≤ 1 / 237800)
    (h_dig_scale : ∀ Y ≥ B, l_dig Y ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
      ∀ i : Fin (l_dig Y), (I_dig i.1).2 ≤ Y ^ 2 / 2 ∧
        ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_dig i.1).1 (I_dig i.1).2).den = 1)
    (h_dig_energy : ∀ q : ℕ, B < q → ∀ δ : ℤ,
      ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
      ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
      16 * Real.log (q : ℝ) ≤
        ∑ k ∈ (Finset.range (l_dig q)) \ (Finset.range (l_dig (q - 1))),
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_dig k).1 (I_dig k).2 : ℝ)))) ^ 2)
    (J : ℕ → ℕ × ℕ)
    (hJ_bounds : ∀ r : ℕ, 495 ≤ (J r).1 ∧ (J r).1 < (J r).2 ∧ (J r).2 ≤ (J r).1 + 2)
    (hJ_sep : ∀ r₁ r₂ : ℕ, r₁ ≠ r₂ → (J r₁).2 + 1 < (J r₂).1 ∨ (J r₂).2 + 1 < (J r₁).1)
    (hJ_growth : ∀ r : ℕ, (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) ≤ (J r).1)
    (hJ_mass : ∀ n : ℕ, ∑ r ∈ Finset.range n, w_Icc (J r).1 (J r).2 ≤ 1 / 237800) :
    ∃ (l_seq : ℕ → ℕ) (I_seq : ℕ → ℕ × ℕ),
      (∀ k : ℕ, 495 ≤ (I_seq k).1 ∧ (I_seq k).1 < (I_seq k).2 ∧ (I_seq k).2 ≤ (I_seq k).1 + 2) ∧
      (∀ k m : ℕ, k ≠ m → (I_seq k).2 + 1 < (I_seq m).1 ∨ (I_seq m).2 + 1 < (I_seq k).1) ∧
      (1 ≤ l_seq B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_seq Y₁ ≤ l_seq Y₂) ∧
      (∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_seq k).1 (I_seq k).2 ≤ 1 / 118900) ∧
      (∀ Y ≥ B, l_seq Y ≤ 2 ^ 57 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
        ∀ i : Fin (l_seq Y), ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_seq i.1).1 (I_seq i.1).2).den = 1) ∧
      (∀ q : ℕ, B < q → ∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        12 * Real.log (q : ℝ) ≤
          ∑ k ∈ (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))),
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)))) ^ 2) ∧
      (∀ r Y : ℕ, (J r).2 ≤ Y → ∃ i : Fin (l_seq Y), I_seq i.1 = J r) :=
by
  classical
  let Good : ℕ → Prop := fun k => ∀ r < (I_dig k).2 + 2, (I_dig k).2 + 1 < (J r).1 ∨ (J r).2 + 1 < (I_dig k).1
  let I_comb : ℕ → ℕ × ℕ := fun x => if x % 2 = 0 then I_dig (x / 2) else J (x / 2)

  have h_pow_r : ∀ r : ℕ, r < (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) ∧ (B + 2) ^ 2 ≤ (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) := by
    intro r
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : 2 ^ r ≤ 2 ^ (20 * (r + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 0 < (B + 2) ^ 2 := by positivity
    have h4 : 2 ^ (20 * (r + 1)) ≤ (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) := Nat.le_mul_of_pos_left _ h3
    have h5 : 0 < 2 ^ (20 * (r + 1)) := by positivity
    exact ⟨lt_of_lt_of_le h1 (le_trans h2 h4), Nat.le_mul_of_pos_right _ h5⟩

  have hGood_global : ∀ k : ℕ, Good k → ∀ r : ℕ, (I_dig k).2 + 1 < (J r).1 ∨ (J r).2 + 1 < (I_dig k).1 := by
    intro k hk r
    by_cases hr : r < (I_dig k).2 + 2
    · exact hk r hr
    · left
      have h1 := (h_pow_r r).1
      have h2 := hJ_growth r
      omega

  have hGood_B : ∀ k < l_dig B, Good k := by
    intro k hk r _
    left
    have hk_ub : (I_dig k).2 ≤ B ^ 2 / 2 := ((h_dig_scale B (le_refl B)).2 ⟨k, hk⟩).1
    have hJr := le_trans (h_pow_r r).2 (hJ_growth r)
    have hB_sq : B ^ 2 + 2 ≤ (B + 2) ^ 2 := by
      calc B ^ 2 + 2 ≤ B ^ 2 + 4 * B + 4 := by omega
        _ = (B + 2) ^ 2 := by ring
    omega

  have hGood_energy : ∀ q : ℕ, B < q → ∀ δ : ℤ,
      ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
      ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
      12 * Real.log (q : ℝ) ≤
        ∑ k ∈ (Finset.Ico (l_dig (q - 1)) (l_dig q)).filter Good,
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_dig k).1 (I_dig k).2 : ℝ)))) ^ 2 := by
    intro q hq δ h_dvd1 h_dvd2
    set S_q := Finset.Ico (l_dig (q - 1)) (l_dig q)
    have h_sdiff : (Finset.range (l_dig q)) \ (Finset.range (l_dig (q - 1))) = S_q := by
      ext k
      simp only [S_q, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
      omega
    set B_q := S_q.filter (fun k => ¬ Good k)
    set f_sin : ℕ → ℝ := fun k =>
      (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_dig k).1 (I_dig k).2 : ℝ)))) ^ 2
    have h_en_full := h_dig_energy q hq δ h_dvd1 h_dvd2
    rw [h_sdiff] at h_en_full
    have h_split := Finset.sum_filter_add_sum_filter_not S_q Good f_sin
    have h_bad_sum : ∑ k ∈ B_q, f_sin k ≤ (B_q.card : ℝ) := by
      have h_le1 : ∀ k ∈ B_q, f_sin k ≤ 1 := fun k _ => Real.sin_sq_le_one _
      have h_s := Finset.sum_le_card_nsmul B_q f_sin 1 h_le1
      simpa using h_s
    set R_q := (Nat.log 2 q) / 10
    set BadPts := (Finset.range R_q).biUnion (fun r => Finset.Icc ((J r).1 - 3) ((J r).1 + 3))
    have h_maps : Set.MapsTo (fun k => (I_dig k).1) (B_q : Set ℕ) (BadPts : Set ℕ) := by
      intro k hk
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hk
      have hk_ub : (I_dig k).2 ≤ q ^ 2 / 2 := ((h_dig_scale q (by omega)).2 ⟨k, hk.1.2⟩).1
      have h_not_good := hk.2
      dsimp [Good] at h_not_good
      push_neg at h_not_good
      obtain ⟨r, _, hr1, hr2⟩ := h_not_good
      have hJr_le : (J r).1 ≤ q ^ 2 := by
        have hq2 : 2 ≤ q ^ 2 := by
          calc 2 ≤ 1189 ^ 2 := by decide
            _ ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      have h_pow_sq : (2 ^ (10 * (r + 1))) ^ 2 ≤ q ^ 2 := by
        have h_eq : (2 ^ (10 * (r + 1))) ^ 2 = 2 ^ (20 * (r + 1)) := by
          rw [← Nat.pow_mul]
          ring_nf
        rw [h_eq]
        have h1 : 0 < (B + 2) ^ 2 := by positivity
        have h2 : 2 ^ (20 * (r + 1)) ≤ (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) := Nat.le_mul_of_pos_left _ h1
        exact le_trans h2 (le_trans (hJ_growth r) hJr_le)
      have h_pow_le_q : 2 ^ (10 * (r + 1)) ≤ q := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp h_pow_sq
      have hq_lt_log : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q
      have h_exp_lt : 10 * (r + 1) < Nat.log 2 q + 1 :=
        (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt h_pow_le_q hq_lt_log)
      have hr_lt_Rq : r < R_q := by
        dsimp [R_q]
        omega
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨r, Finset.mem_range.mpr hr_lt_Rq, ?_⟩
      dsimp only
      rw [Finset.mem_Icc]
      have hdb := h_dig_bounds k
      have hJb := hJ_bounds r
      omega
    have h_inj : Set.InjOn (fun k => (I_dig k).1) (B_q : Set ℕ) := by
      intro k₁ _ k₂ _ h_eq
      dsimp only at h_eq
      by_contra h_ne
      have h_sep := h_dig_sep k₁ k₂ h_ne
      have hb1 := h_dig_bounds k₁
      have hb2 := h_dig_bounds k₂
      omega
    have h_card1 : B_q.card ≤ BadPts.card := Finset.card_le_card_of_injOn (fun k => (I_dig k).1) h_maps h_inj
    have h_card2 : BadPts.card ≤ ∑ r ∈ Finset.range R_q, (Finset.Icc ((J r).1 - 3) ((J r).1 + 3)).card :=
      Finset.card_biUnion_le
    have h_Icc_7 : ∀ r ∈ Finset.range R_q, (Finset.Icc ((J r).1 - 3) ((J r).1 + 3)).card ≤ 7 := by
      intro r _
      rw [Nat.card_Icc]
      have := (hJ_bounds r).1
      omega
    have h_card3 : ∑ r ∈ Finset.range R_q, (Finset.Icc ((J r).1 - 3) ((J r).1 + 3)).card ≤ 7 * R_q := by
      have h := Finset.sum_le_card_nsmul (Finset.range R_q) (fun r => (Finset.Icc ((J r).1 - 3) ((J r).1 + 3)).card) 7 h_Icc_7
      simpa [mul_comm] using h
    have h_card_log : B_q.card ≤ Nat.log 2 q := by
      have : 7 * R_q ≤ Nat.log 2 q := by dsimp [R_q]; omega
      omega
    set L := Nat.log 2 q
    have h2L_le : 2 ^ L ≤ q := Nat.pow_log_le_self 2 (by omega)
    have h_log_pow : (L : ℝ) * Real.log 2 ≤ Real.log (q : ℝ) := by
      have h1 : Real.log ((2 : ℝ) ^ L) ≤ Real.log (q : ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast h2L_le
      rwa [Real.log_pow] at h1
    have h_log2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h_exp := Real.add_one_le_exp (- Real.log 2)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h_exp
      linarith
    have h_log_pos : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
    have h_Bq_real : (B_q.card : ℝ) ≤ 4 * Real.log (q : ℝ) := by
      have h1 : (B_q.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast h_card_log
      have h2 : (L : ℝ) * (1 / 2 : ℝ) ≤ (L : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left h_log2_ge (Nat.cast_nonneg L)
      linarith
    linarith

  let S_good : ℕ → Finset ℕ := fun q =>
    if q < B then ∅
    else if q = B then (Finset.range (l_dig B)).filter Good
    else (Finset.Ico (l_dig (q - 1)) (l_dig q)).filter Good
  let D_good : ℕ → Finset ℕ := fun q => (S_good q).image (fun k => 2 * k)
  let G_raw : ℕ → Finset ℕ := fun q =>
    if q ≤ B then ∅ else (Finset.range q).filter (fun r => (J r).2 = q)
  let G_slice : ℕ → Finset ℕ := fun q => (G_raw q).image (fun r => 2 * r + 1)
  let W : ℕ → Finset ℕ := fun q => D_good q ∪ G_slice q

  have hS_props : ∀ q x : ℕ, x ∈ S_good q → B ≤ q ∧ Good x ∧ x < l_dig q ∧ (B < q → l_dig (q - 1) ≤ x) := by
    intro q x hx
    dsimp [S_good] at hx
    split_ifs at hx with hlt heq
    · simp at hx
    · rw [Finset.mem_filter, Finset.mem_range] at hx
      exact ⟨by omega, hx.2, heq.symm ▸ hx.1, by omega⟩
    · rw [Finset.mem_filter, Finset.mem_Ico] at hx
      exact ⟨by omega, hx.2, hx.1.2, fun _ => hx.1.1⟩

  have hG_props : ∀ q r : ℕ, r ∈ G_raw q → B < q ∧ (J r).2 = q := by
    intro q r hr
    dsimp [G_raw] at hr
    split_ifs at hr with hle
    · simp at hr
    · rw [Finset.mem_filter, Finset.mem_range] at hr
      exact ⟨by omega, hr.2⟩

  have hW_cases : ∀ q x : ℕ, x ∈ W q →
      (x % 2 = 0 ∧ x / 2 ∈ S_good q ∧ I_comb x = I_dig (x / 2)) ∨
      (x % 2 = 1 ∧ x / 2 ∈ G_raw q ∧ I_comb x = J (x / 2)) := by
    intro q x hx
    rw [Finset.mem_union] at hx
    rcases hx with hxD | hxG
    · left
      rw [Finset.mem_image] at hxD
      obtain ⟨k, hk, rfl⟩ := hxD
      have h_mod : (2 * k) % 2 = 0 := by omega
      have h_div : (2 * k) / 2 = k := by omega
      refine ⟨h_mod, ?_, ?_⟩
      · rwa [h_div]
      · dsimp [I_comb]; rw [if_pos h_mod, h_div]
    · right
      rw [Finset.mem_image] at hxG
      obtain ⟨r, hr, rfl⟩ := hxG
      have h_mod : (2 * r + 1) % 2 = 1 := by omega
      have h_mod_ne : (2 * r + 1) % 2 ≠ 0 := by omega
      have h_div : (2 * r + 1) / 2 = r := by omega
      refine ⟨h_mod, ?_, ?_⟩
      · rwa [h_div]
      · dsimp [I_comb]; rw [if_neg h_mod_ne, h_div]

  have hW_B_card : 1 ≤ (W B).card := by
    refine Finset.card_pos.mpr ⟨0, ?_⟩
    rw [Finset.mem_union]
    left
    rw [Finset.mem_image]
    refine ⟨0, ?_, by omega⟩
    dsimp [S_good]
    rw [if_neg (by omega : ¬ B < B), if_pos rfl, Finset.mem_filter, Finset.mem_range]
    exact ⟨h_dig_mono.1, hGood_B 0 h_dig_mono.1⟩

  have hW_bounds : ∀ q ≥ B, ∀ x ∈ W q, 495 ≤ (I_comb x).1 ∧ (I_comb x).1 < (I_comb x).2 ∧ (I_comb x).2 ≤ (I_comb x).1 + 2 := by
    intro q _ x hx
    rcases hW_cases q x hx with ⟨_, _, hI⟩ | ⟨_, _, hI⟩
    · rw [hI]; exact h_dig_bounds (x / 2)
    · rw [hI]; exact hJ_bounds (x / 2)

  have hW_sep : ∀ q₁ ≥ B, ∀ q₂ ≥ B, ∀ x₁ ∈ W q₁, ∀ x₂ ∈ W q₂, (q₁ ≠ q₂ ∨ x₁ ≠ x₂) →
      x₁ ≠ x₂ ∧ ((I_comb x₁).2 + 1 < (I_comb x₂).1 ∨ (I_comb x₂).2 + 1 < (I_comb x₁).1) := by
    intro q₁ hq₁ q₂ hq₂ x₁ hx₁ x₂ hx₂ h_diff
    have hx_ne : x₁ ≠ x₂ := by
      rcases h_diff with hq_ne | hx_ne
      · intro h_eq
        subst h_eq
        rcases hW_cases q₁ x₁ hx₁ with ⟨hm1, hS1, _⟩ | ⟨hm1, hG1, _⟩ <;>
        rcases hW_cases q₂ x₁ hx₂ with ⟨hm2, hS2, _⟩ | ⟨hm2, hG2, _⟩
        · have hp1 := hS_props q₁ (x₁ / 2) hS1
          have hp2 := hS_props q₂ (x₁ / 2) hS2
          rcases lt_or_gt_of_ne hq_ne with hlt | hgt
          · have hm := h_dig_mono.2 q₁ (q₂ - 1) (by omega)
            have hlow := hp2.2.2.2 (by omega)
            omega
          · have hm := h_dig_mono.2 q₂ (q₁ - 1) (by omega)
            have hlow := hp1.2.2.2 (by omega)
            omega
        · omega
        · omega
        · have hp1 := (hG_props q₁ (x₁ / 2) hG1).2
          have hp2 := (hG_props q₂ (x₁ / 2) hG2).2
          omega
      · exact hx_ne
    refine ⟨hx_ne, ?_⟩
    rcases hW_cases q₁ x₁ hx₁ with ⟨hm1, hS1, hI1⟩ | ⟨hm1, hG1, hI1⟩ <;>
    rcases hW_cases q₂ x₂ hx₂ with ⟨hm2, hS2, hI2⟩ | ⟨hm2, hG2, hI2⟩
    · rw [hI1, hI2]
      exact h_dig_sep (x₁ / 2) (x₂ / 2) (by omega)
    · rw [hI1, hI2]
      exact hGood_global (x₁ / 2) (hS_props q₁ (x₁ / 2) hS1).2.1 (x₂ / 2)
    · rw [hI1, hI2]
      exact (hGood_global (x₂ / 2) (hS_props q₂ (x₂ / 2) hS2).2.1 (x₁ / 2)).symm
    · rw [hI1, hI2]
      exact hJ_sep (x₁ / 2) (x₂ / 2) (by omega)

  have hW_gad : ∀ r : ℕ, B < (J r).2 ∧ 2 * r + 1 ∈ W (J r).2 := by
    intro r
    have hr_lt : r < (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) := (h_pow_r r).1
    have hB_le : (B + 2) ^ 2 ≤ (B + 2) ^ 2 * 2 ^ (20 * (r + 1)) := (h_pow_r r).2
    have hB_lt : B < (B + 2) ^ 2 := by
      calc B < B + 4 := by omega
        _ ≤ B ^ 2 + 4 * B + 4 := by omega
        _ = (B + 2) ^ 2 := by ring
    have hJr1 := hJ_growth r
    have hJr2 := (hJ_bounds r).2.1
    have hq_gt_B : B < (J r).2 := by omega
    have hr_lt_q : r < (J r).2 := by omega
    refine ⟨hq_gt_B, ?_⟩
    rw [Finset.mem_union]
    right
    rw [Finset.mem_image]
    refine ⟨r, ?_, rfl⟩
    dsimp [G_raw]
    rw [if_neg (by omega : ¬ (J r).2 ≤ B), Finset.mem_filter, Finset.mem_range]
    exact ⟨hr_lt_q, rfl⟩

  let l_seq : ℕ → ℕ := fun Y => ∑ q ∈ Finset.Icc B Y, (W q).card
  have hl_mono : ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_seq Y₁ ≤ l_seq Y₂ := by
    intro Y₁ Y₂ h12
    exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right h12)
  have hl_lt_B : ∀ Y < B, l_seq Y = 0 := by
    intro Y hY
    dsimp [l_seq]
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  have hl_B : l_seq B = (W B).card := by
    dsimp [l_seq]
    rw [Finset.Icc_self, Finset.sum_singleton]
  have hl_step : ∀ q ≥ B, l_seq q = l_seq (q - 1) + (W q).card := by
    intro q hq
    dsimp [l_seq]
    have h_ins : Finset.Icc B q = insert q (Finset.Icc B (q - 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not : q ∉ Finset.Icc B (q - 1) := by
      rw [Finset.mem_Icc]
      omega
    rw [h_ins, Finset.sum_insert h_not]
    omega

  have h_unb : ∀ k : ℕ, ∃ Y : ℕ, k < l_seq Y := by
    intro k
    induction k with
    | zero =>
      refine ⟨B, ?_⟩
      rw [hl_B]
      exact hW_B_card
    | succ k ih =>
      obtain ⟨Y, hkY⟩ := ih
      have hBY : B ≤ Y := by
        by_contra h_lt
        have := hl_lt_B Y (by omega)
        omega
      set r := Y + 1
      set Y' := (J r).2
      have hr_lt_Jr : r < (J r).1 := lt_of_lt_of_le (h_pow_r r).1 (hJ_growth r)
      have hY_lt_Y' : Y < Y' := by
        have := (hJ_bounds r).2.1
        omega
      have hW_pos : 1 ≤ (W Y').card := Finset.card_pos.mpr ⟨2 * r + 1, (hW_gad r).2⟩
      have h_le_prev : l_seq Y ≤ l_seq (Y' - 1) := hl_mono Y (Y' - 1) (by omega)
      have h_st := hl_step Y' (by omega)
      refine ⟨Y', by omega⟩

  let q_of : ℕ → ℕ := fun k => Nat.find (h_unb k)
  have hq_spec : ∀ k : ℕ, k < l_seq (q_of k) := fun k => Nat.find_spec (h_unb k)
  have hq_min : ∀ k Y : ℕ, k < l_seq Y → q_of k ≤ Y := fun k Y h => Nat.find_min' (h_unb k) h
  have hq_ge_B : ∀ k : ℕ, B ≤ q_of k := by
    intro k
    by_contra h_lt
    have h1 := hl_lt_B (q_of k) (by omega)
    have h2 := hq_spec k
    omega
  have hq_lower : ∀ k : ℕ, l_seq (q_of k - 1) ≤ k := by
    intro k
    have hB_le := hq_ge_B k
    have h_lt : q_of k - 1 < q_of k := by omega
    exact not_lt.mp (Nat.find_min (h_unb k) h_lt)
  have hr_lt : ∀ k : ℕ, k - l_seq (q_of k - 1) < (W (q_of k)).card := by
    intro k
    have h1 := hq_spec k
    have h2 := hq_lower k
    have h3 := hl_step (q_of k) (hq_ge_B k)
    omega

  let elem_of : ℕ → ℕ → ℕ := fun q r =>
    if hr : r < (W q).card then ((W q).equivFin.symm ⟨r, hr⟩).1 else 0
  let x_of : ℕ → ℕ := fun k => elem_of (q_of k) (k - l_seq (q_of k - 1))
  let I_seq : ℕ → ℕ × ℕ := fun k => I_comb (x_of k)

  have hx_mem : ∀ k : ℕ, x_of k ∈ W (q_of k) := by
    intro k
    dsimp [x_of, elem_of]
    rw [dif_pos (hr_lt k)]
    exact ((W (q_of k)).equivFin.symm ⟨_, hr_lt k⟩).2

  have hq_eq_of_slice : ∀ q ≥ B, ∀ k : ℕ, l_seq (q - 1) ≤ k → k < l_seq q → q_of k = q := by
    intro q hq k hk1 hk2
    have hle : q_of k ≤ q := hq_min k q hk2
    by_contra hne
    have hlt : q_of k ≤ q - 1 := by omega
    have h_m := hl_mono (q_of k) (q - 1) hlt
    have h_s := hq_spec k
    omega

  have hx_inj : ∀ k m : ℕ, k ≠ m → x_of k ≠ x_of m := by
    intro k m hkm h_eq
    have hq_eq : q_of k = q_of m := by
      by_contra hq_ne
      exact (hW_sep (q_of k) (hq_ge_B k) (q_of m) (hq_ge_B m) (x_of k) (hx_mem k) (x_of m) (hx_mem m) (Or.inl hq_ne)).1 h_eq
    set q := q_of k
    have hrk : k - l_seq (q - 1) < (W q).card := hr_lt k
    have hrm : m - l_seq (q - 1) < (W q).card := by rw [hq_eq]; exact hr_lt m
    have h_eq' : elem_of q (k - l_seq (q - 1)) = elem_of q (m - l_seq (q - 1)) := by
      dsimp [x_of] at h_eq
      rw [← hq_eq] at h_eq
      exact h_eq
    dsimp [elem_of] at h_eq'
    rw [dif_pos hrk, dif_pos hrm] at h_eq'
    have h_sub_eq := ((W q).equivFin.symm).injective (Subtype.ext h_eq')
    have h_idx_eq : k - l_seq (q - 1) = m - l_seq (q - 1) := congr_arg Fin.val h_sub_eq
    have h_low_k : l_seq (q - 1) ≤ k := hq_lower k
    have h_low_m : l_seq (q - 1) ≤ m := by rw [hq_eq]; exact hq_lower m
    omega

  refine ⟨l_seq, I_seq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hW_bounds (q_of k) (hq_ge_B k) (x_of k) (hx_mem k)
  · intro k m hkm
    exact (hW_sep (q_of k) (hq_ge_B k) (q_of m) (hq_ge_B m) (x_of k) (hx_mem k) (x_of m) (hx_mem m) (Or.inr (hx_inj k m hkm))).2
  · exact ⟨by rw [hl_B]; exact hW_B_card, hl_mono⟩
  · intro n
    set N := 1 + (Finset.range n).sup x_of
    set E_N := (Finset.range N).image (fun k => 2 * k)
    set O_N := (Finset.range N).image (fun r => 2 * r + 1)
    have h_disj : Disjoint E_N O_N := by
      rw [Finset.disjoint_left]
      intro x hxE hxO
      rw [Finset.mem_image] at hxE hxO
      obtain ⟨k, _, rfl⟩ := hxE
      obtain ⟨r, _, h_eq⟩ := hxO
      omega
    have h_sub : (Finset.range n).image x_of ⊆ E_N ∪ O_N := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hx_le : x_of i ≤ (Finset.range n).sup x_of := Finset.le_sup hi
      have hx_div : x_of i / 2 < N := by dsimp [N]; omega
      rw [Finset.mem_union]
      rcases Nat.mod_two_eq_zero_or_one (x_of i) with h0 | h1
      · left
        rw [Finset.mem_image]
        refine ⟨x_of i / 2, Finset.mem_range.mpr hx_div, by omega⟩
      · right
        rw [Finset.mem_image]
        refine ⟨x_of i / 2, Finset.mem_range.mpr hx_div, by omega⟩
    have h_inj_on : Set.InjOn x_of (Finset.range n : Set ℕ) := by
      intro a _ b _ hab
      by_contra hne
      exact hx_inj a b hne hab
    have h_sum_img : ∑ k ∈ Finset.range n, w_Icc (I_comb (x_of k)).1 (I_comb (x_of k)).2 =
        ∑ x ∈ (Finset.range n).image x_of, w_Icc (I_comb x).1 (I_comb x).2 :=
      (Finset.sum_image (f := fun x => w_Icc (I_comb x).1 (I_comb x).2) h_inj_on).symm
    have h_nonneg : ∀ x : ℕ, 0 ≤ w_Icc (I_comb x).1 (I_comb x).2 := by
      intro x
      apply Finset.sum_nonneg
      intro m _
      positivity
    have h_le_union : ∑ x ∈ (Finset.range n).image x_of, w_Icc (I_comb x).1 (I_comb x).2 ≤
        ∑ x ∈ E_N ∪ O_N, w_Icc (I_comb x).1 (I_comb x).2 :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun x _ _ => h_nonneg x)
    rw [Finset.sum_union h_disj] at h_le_union
    have h_sum_E : ∑ x ∈ E_N, w_Icc (I_comb x).1 (I_comb x).2 =
        ∑ k ∈ Finset.range N, w_Icc (I_dig k).1 (I_dig k).2 := by
      have h_inj2 : Set.InjOn (fun k => 2 * k) (Finset.range N : Set ℕ) := by
        intro a _ b _ h; dsimp only at h; omega
      rw [Finset.sum_image h_inj2]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h_mod : (2 * k) % 2 = 0 := by omega
      have h_div : (2 * k) / 2 = k := by omega
      dsimp [I_comb]
      rw [if_pos h_mod, h_div]
    have h_sum_O : ∑ x ∈ O_N, w_Icc (I_comb x).1 (I_comb x).2 =
        ∑ r ∈ Finset.range N, w_Icc (J r).1 (J r).2 := by
      have h_inj2 : Set.InjOn (fun r => 2 * r + 1) (Finset.range N : Set ℕ) := by
        intro a _ b _ h; dsimp only at h; omega
      rw [Finset.sum_image h_inj2]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      have h_mod : (2 * r + 1) % 2 ≠ 0 := by omega
      have h_div : (2 * r + 1) / 2 = r := by omega
      dsimp [I_comb]
      rw [if_neg h_mod, h_div]
    have h1 := h_dig_mass N
    have h2 := hJ_mass N
    change ∑ k ∈ Finset.range n, w_Icc (I_comb (x_of k)).1 (I_comb (x_of k)).2 ≤ 1 / 118900
    linarith
  · intro Y hBY
    refine ⟨?_, ?_⟩
    · have hG_card : ∀ q > B, (G_raw q).card ≤ 1 := by
        intro q hq
        rw [Finset.card_le_one_iff]
        intro r₁ r₂ hr₁ hr₂
        have hp1 := (hG_props q r₁ hr₁).2
        have hp2 := (hG_props q r₂ hr₂).2
        by_contra h_ne
        have h_sep := hJ_sep r₁ r₂ h_ne
        have hb1 := hJ_bounds r₁
        have hb2 := hJ_bounds r₂
        omega
      have hW_step : ∀ q > B, (W q).card ≤ (l_dig q - l_dig (q - 1)) + 1 := by
        intro q hq
        have h1 : (W q).card ≤ (D_good q).card + (G_slice q).card := Finset.card_union_le _ _
        have h2 : (D_good q).card ≤ (S_good q).card := Finset.card_image_le
        have h3 : (G_slice q).card ≤ (G_raw q).card := Finset.card_image_le
        have h4 : (S_good q).card ≤ l_dig q - l_dig (q - 1) := by
          dsimp [S_good]
          rw [if_neg (by omega : ¬ q < B), if_neg (by omega : ¬ q = B)]
          exact le_trans (Finset.card_filter_le _ _) (by rw [Nat.card_Ico])
        have h5 := hG_card q hq
        omega
      have hW_B_le : (W B).card ≤ l_dig B := by
        have h1 : (W B).card ≤ (D_good B).card + (G_slice B).card := Finset.card_union_le _ _
        have h2 : (D_good B).card ≤ (S_good B).card := Finset.card_image_le
        have h3 : (S_good B).card ≤ l_dig B := by
          dsimp [S_good]
          rw [if_neg (by omega : ¬ B < B), if_pos rfl]
          exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
        have h4 : (G_slice B).card = 0 := by
          dsimp [G_slice, G_raw]
          rw [if_pos (le_refl B), Finset.image_empty, Finset.card_empty]
        omega
      have h_ind : ∀ d : ℕ, ∑ q ∈ Finset.Icc B (B + d), (W q).card ≤ l_dig (B + d) + d := by
        intro d
        induction d with
        | zero =>
          rw [Nat.add_zero, Finset.Icc_self, Finset.sum_singleton]
          exact hW_B_le
        | succ d ih =>
          set q := B + (d + 1)
          have h_ins : Finset.Icc B q = insert q (Finset.Icc B (B + d)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have h_not : q ∉ Finset.Icc B (B + d) := by rw [Finset.mem_Icc]; omega
          rw [h_ins, Finset.sum_insert h_not]
          have h_st := hW_step q (by omega)
          have hq_prev : q - 1 = B + d := by omega
          rw [hq_prev] at h_st
          have h_mono := h_dig_mono.2 (B + d) q (by omega)
          omega
      have h_sum_Y : l_seq Y ≤ l_dig Y + (Y - B) := by
        dsimp [l_seq]
        have h := h_ind (Y - B)
        rwa [Nat.add_sub_of_le hBY] at h
      have hl_ub : l_dig Y ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 := (h_dig_scale Y hBY).1
      have hY_ub : Y - B ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 := by
        have h1 : Y - B ≤ Y := Nat.sub_le Y B
        have h2 : 0 < 2 ^ 56 * (Nat.log 2 Y + 1) ^ 3 := by positivity
        have h3 : Y ≤ Y * (2 ^ 56 * (Nat.log 2 Y + 1) ^ 3) := Nat.le_mul_of_pos_right Y h2
        calc Y - B ≤ Y * (2 ^ 56 * (Nat.log 2 Y + 1) ^ 3) := le_trans h1 h3
          _ = 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 := by ring
      calc l_seq Y
          ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 + 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 := by omega
        _ = 2 ^ 57 * Y * (Nat.log 2 Y + 1) ^ 3 := by ring
    · intro i
      set q := q_of i.1
      set x := x_of i.1
      have hqB : B ≤ q := hq_ge_B i.1
      have hqY : q ≤ Y := hq_min i.1 Y i.2
      have hx : x ∈ W q := hx_mem i.1
      change ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_comb x).1 (I_comb x).2).den = 1
      rcases hW_cases q x hx with ⟨_, hS, hI⟩ | ⟨_, hG, hI⟩
      · rw [hI]
        have hk_lt_q : x / 2 < l_dig q := (hS_props q (x / 2) hS).2.2.1
        have hk_lt_Y : x / 2 < l_dig Y := lt_of_lt_of_le hk_lt_q (h_dig_mono.2 q Y hqY)
        exact ((h_dig_scale Y hBY).2 ⟨x / 2, hk_lt_Y⟩).2
      · rw [hI]
        set r := x / 2
        have hJr_eq : (J r).2 = q := (hG_props q r hG).2
        have hJr_bounds := hJ_bounds r
        set D := (Finset.Icc 1 Y).lcm id
        have h_term : ∀ n ∈ Finset.Icc (J r).1 (J r).2,
            (D : ℚ) * (n : ℚ)⁻¹ = ((D / n : ℕ) : ℚ) := by
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hn_mem : n ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have h_dvd : n ∣ D := Finset.dvd_lcm hn_mem
          have h_mul : n * (D / n) = D := Nat.mul_div_cancel' h_dvd
          have hn_pos : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
          calc (D : ℚ) * (n : ℚ)⁻¹
              = ((n * (D / n) : ℕ) : ℚ) * (n : ℚ)⁻¹ := by rw [h_mul]
            _ = (n : ℚ) * ((D / n : ℕ) : ℚ) * (n : ℚ)⁻¹ := by push_cast; ring
            _ = ((D / n : ℕ) : ℚ) := by rw [mul_right_comm, mul_inv_cancel₀ hn_pos, one_mul]
        have h_sum_eq : (D : ℚ) * w_Icc (J r).1 (J r).2 =
            ((∑ n ∈ Finset.Icc (J r).1 (J r).2, (D / n) : ℕ) : ℚ) := by
          dsimp [w_Icc]
          rw [Finset.mul_sum, Finset.sum_congr rfl h_term, Nat.cast_sum]
        rw [h_sum_eq, Rat.den_natCast]
  · intro q hq δ h_dvd1 h_dvd2
    set f_comb : ℕ → ℝ := fun x =>
      (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_comb x).1 (I_comb x).2 : ℝ)))) ^ 2
    have h_sdiff : (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))) = Finset.Ico (l_seq (q - 1)) (l_seq q) := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
      omega
    have h_congr : ∀ k ∈ Finset.Ico (l_seq (q - 1)) (l_seq q),
        f_comb (x_of k) = f_comb (elem_of q (k - l_seq (q - 1))) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hqk : q_of k = q := hq_eq_of_slice q (by omega) k hk.1 hk.2
      dsimp [x_of]
      rw [hqk]
    have h_slice_sum : ∑ k ∈ (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))), f_comb (x_of k) =
        ∑ x ∈ W q, f_comb x := by
      rw [h_sdiff, Finset.sum_congr rfl h_congr, Finset.sum_Ico_eq_sum_range]
      have h_diff_eq : l_seq q - l_seq (q - 1) = (W q).card := by
        have := hl_step q (by omega)
        omega
      rw [h_diff_eq]
      have h_cancel : ∀ x ∈ Finset.range (W q).card,
          f_comb (elem_of q (l_seq (q - 1) + x - l_seq (q - 1))) = f_comb (elem_of q x) := by
        intro x _
        rw [Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl h_cancel, ← Fin.sum_univ_eq_sum_range]
      have h_fin_eq : ∀ i : Fin (W q).card,
          f_comb (elem_of q i.1) = f_comb ((W q).equivFin.symm i).1 := by
        intro i
        dsimp [elem_of]
        rw [if_pos i.2]
      rw [Finset.sum_congr rfl (fun i _ => h_fin_eq i)]
      exact (Finset.sum_equiv (W q).equivFin.symm (by simp) (by simp)).trans
        (Finset.sum_attach (W q) f_comb)
    change 12 * Real.log (q : ℝ) ≤ ∑ k ∈ (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))), f_comb (x_of k)
    rw [h_slice_sum]
    have h_sub : D_good q ⊆ W q := Finset.subset_union_left
    have h_le_W : ∑ x ∈ D_good q, f_comb x ≤ ∑ x ∈ W q, f_comb x :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => sq_nonneg _)
    have h_inj2 : Set.InjOn (fun k => 2 * k) (S_good q : Set ℕ) := by
      intro a _ b _ h; dsimp only at h; omega
    have h_eq_D : ∑ x ∈ D_good q, f_comb x =
        ∑ k ∈ (Finset.Ico (l_dig (q - 1)) (l_dig q)).filter Good,
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_dig k).1 (I_dig k).2 : ℝ)))) ^ 2 := by
      dsimp [D_good]
      rw [Finset.sum_image h_inj2]
      have hS_eq : S_good q = (Finset.Ico (l_dig (q - 1)) (l_dig q)).filter Good := by
        dsimp [S_good]
        rw [if_neg (by omega : ¬ q < B), if_neg (by omega : ¬ q = B)]
      rw [hS_eq]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h_mod : (2 * k) % 2 = 0 := by omega
      have h_div : (2 * k) / 2 = k := by omega
      dsimp [f_comb, I_comb]
      rw [if_pos h_mod, h_div]
    have h_en_good := hGood_energy q hq δ h_dvd1 h_dvd2
    linarith
  · intro r Y hJrY
    set q := (J r).2
    have hqB : B < q := (hW_gad r).1
    have h_in : 2 * r + 1 ∈ W q := (hW_gad r).2
    let idx := (W q).equivFin ⟨2 * r + 1, h_in⟩
    let k := l_seq (q - 1) + idx.1
    have hk_lt_q : k < l_seq q := by
      have h_st := hl_step q (by omega)
      have := idx.2
      omega
    have hk_lt_Y : k < l_seq Y := lt_of_lt_of_le hk_lt_q (hl_mono q Y hJrY)
    refine ⟨⟨k, hk_lt_Y⟩, ?_⟩
    have hqk : q_of k = q := hq_eq_of_slice q (by omega) k (by omega) hk_lt_q
    have h_sub : k - l_seq (q - 1) = idx.1 := Nat.add_sub_cancel_left _ _
    have hx_eq : x_of k = 2 * r + 1 := by
      change elem_of (q_of k) (k - l_seq (q_of k - 1)) = 2 * r + 1
      rw [hqk, h_sub]
      dsimp [elem_of]
      rw [if_pos idx.2]
      have h_symm : (W q).equivFin.symm idx = ⟨2 * r + 1, h_in⟩ := by
        exact (W q).equivFin.symm_apply_apply ⟨2 * r + 1, h_in⟩
      exact congr_arg Subtype.val h_symm
    change I_comb (x_of k) = J r
    rw [hx_eq]
    have h_mod : (2 * r + 1) % 2 ≠ 0 := by omega
    have h_div : (2 * r + 1) / 2 = r := by omega
    dsimp [I_comb]
    rw [if_neg h_mod, h_div]

theorem lacunary_gadget_integer_rigidity_lock (B : ℕ) (hB : 1189 ≤ B)
    (l_seq : ℕ → ℕ) (I_seq : ℕ → ℕ × ℕ)
    (h_bounds : ∀ k : ℕ, 495 ≤ (I_seq k).1 ∧ (I_seq k).1 < (I_seq k).2 ∧ (I_seq k).2 ≤ (I_seq k).1 + 2)
    (h_sep : ∀ k m : ℕ, k ≠ m → (I_seq k).2 + 1 < (I_seq m).1 ∨ (I_seq m).2 + 1 < (I_seq k).1)
    (h_mono : 1 ≤ l_seq B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_seq Y₁ ≤ l_seq Y₂)
    (h_scale_lcm : ∀ Y ≥ B, l_seq Y ≤ 2 ^ 57 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
      ∀ i : Fin (l_seq Y), ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_seq i.1).1 (I_seq i.1).2).den = 1)
    (J : ℕ → ℕ × ℕ) (p_idx : ℕ → ℕ → ℕ)
    (hJ_bounds : ∀ r : ℕ, 495 ≤ (J r).1 ∧ (J r).1 < (J r).2 ∧ (J r).2 ≤ (J r).1 + 2)
    (hJ_sep : ∀ r₁ r₂ : ℕ, r₁ ≠ r₂ → (J r₁).2 + 1 < (J r₂).1 ∨ (J r₂).2 + 1 < (J r₁).1)
    (hp_inj : ∀ m₁ j₁ m₂ j₂ : ℕ, p_idx m₁ j₁ = p_idx m₂ j₂ → m₁ = m₂ ∧ j₁ = j₂)
    (hJ_ident : ∀ m j : ℕ,
      let p := p_idx m j
      let m_val := (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))
      (J (3 * p)).2 ≤ 7135 * m_val ∧
      (J (3 * p + 1)).2 ≤ 7135 * m_val ∧
      (J (3 * p + 2)).2 ≤ 7135 * m_val ∧
      2 * (1189 * w_Icc (J (3 * p)).1 (J (3 * p)).2) +
        3 * (1189 * w_Icc (J (3 * p + 1)).1 (J (3 * p + 1)).2) -
        6 * (1189 * w_Icc (J (3 * p + 2)).1 (J (3 * p + 2)).2) = (m_val : ℚ)⁻¹)
    (h_gadget_mem : ∀ r Y : ℕ, (J r).2 ≤ Y → ∃ i : Fin (l_seq Y), I_seq i.1 = J r)
    (M : ℝ) (hM : 0 < M)
    (c : ℕ → ℤ)
    (hc_compat : ∀ d₁ d₂ : ℕ, 0 < d₁ → 0 < d₂ → d₁ ∣ d₂ → (d₁ : ℤ) ∣ (c d₂ - c d₁))
    (hc_energy : ∀ Y d : ℕ, Y ≤ d →
      ∑ i : Fin (l_seq Y),
        (Real.sin (Real.pi * (c d : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ M) :
    ∃ a_star : ℤ,
      (∀ d : ℕ, 0 < d → (d : ℤ) ∣ (c d - a_star)) ∧
      (∀ Y ≥ B, ∑ i : Fin (l_seq Y),
        (Real.sin (Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ M) :=
by
  classical
  have h_sin_add_int_mul_pi_sq : ∀ (x : ℝ) (k : ℤ),
      (Real.sin (x + (k : ℝ) * Real.pi)) ^ 2 = (Real.sin x) ^ 2 := by
    intro x k
    rw [← sq_abs (Real.sin (x + _)), Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one,
      one_zpow, one_mul, sq_abs]

  have h_jordan_sin_sq_bound : ∀ (δ : ℝ), -(1 / 2) ≤ δ → δ ≤ 1 / 2 →
      4 * δ ^ 2 ≤ (Real.sin (Real.pi * δ)) ^ 2 := by
    intro δ h1 h2
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have habs_δ : |δ| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, h2⟩
    have habs : |Real.pi * δ| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos hpi_pos]
      nlinarith
    have hj := Real.mul_abs_le_abs_sin habs
    have h_two : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
      have h_eq : 2 / Real.pi * |Real.pi * δ| = 2 * |δ| := by
        rw [abs_mul, abs_of_pos hpi_pos]
        field_simp [ne_of_gt hpi_pos]
      rwa [h_eq] at hj
    have h_sq : (2 * |δ|) ^ 2 ≤ |Real.sin (Real.pi * δ)| ^ 2 := by
      nlinarith [abs_nonneg δ, abs_nonneg (Real.sin (Real.pi * δ))]
    calc 4 * δ ^ 2 = 4 * |δ| ^ 2 := by rw [sq_abs]
      _ = (2 * |δ|) ^ 2 := by ring
      _ ≤ |Real.sin (Real.pi * δ)| ^ 2 := h_sq
      _ = (Real.sin (Real.pi * δ)) ^ 2 := sq_abs _

  have h_sin_two_three_six_sq : ∀ (α β γ : ℝ),
      (Real.sin (2 * α + 3 * β - 6 * γ)) ^ 2 ≤
        49 * ((Real.sin α) ^ 2 + (Real.sin β) ^ 2 + (Real.sin γ) ^ 2) := by
    intro α β γ
    have h_add : ∀ x y : ℝ, |Real.sin (x + y)| ≤ |Real.sin x| + |Real.sin y| := by
      intro x y
      rw [Real.sin_add]
      calc |Real.sin x * Real.cos y + Real.cos x * Real.sin y|
          ≤ |Real.sin x * Real.cos y| + |Real.cos x * Real.sin y| := abs_add_le _ _
        _ = |Real.sin x| * |Real.cos y| + |Real.cos x| * |Real.sin y| := by rw [abs_mul, abs_mul]
        _ ≤ |Real.sin x| * 1 + 1 * |Real.sin y| := by
            gcongr
            · exact Real.abs_cos_le_one y
            · exact Real.abs_cos_le_one x
        _ = |Real.sin x| + |Real.sin y| := by ring
    have h2 : ∀ x : ℝ, |Real.sin (2 * x)| ≤ 2 * |Real.sin x| := by
      intro x
      have := h_add x x
      ring_nf at this ⊢
      exact this
    have h3 : ∀ x : ℝ, |Real.sin (3 * x)| ≤ 3 * |Real.sin x| := by
      intro x
      have h_split : 3 * x = 2 * x + x := by ring
      rw [h_split]
      linarith [h_add (2 * x) x, h2 x]
    have h6 : ∀ x : ℝ, |Real.sin (6 * x)| ≤ 6 * |Real.sin x| := by
      intro x
      have h_split : 6 * x = 3 * x + 3 * x := by ring
      rw [h_split]
      linarith [h_add (3 * x) (3 * x), h3 x]
    have h_tot : |Real.sin (2 * α + 3 * β - 6 * γ)| ≤
        2 * |Real.sin α| + 3 * |Real.sin β| + 6 * |Real.sin γ| := by
      have h_sub : 2 * α + 3 * β - 6 * γ = (2 * α + 3 * β) + (- (6 * γ)) := by ring
      rw [h_sub]
      have ha1 := h_add (2 * α + 3 * β) (- (6 * γ))
      rw [Real.sin_neg, abs_neg] at ha1
      have ha2 := h_add (2 * α) (3 * β)
      linarith [h2 α, h3 β, h6 γ]
    set a := |Real.sin α|
    set b := |Real.sin β|
    set c_abs := |Real.sin γ|
    have h_sq1 : (Real.sin (2 * α + 3 * β - 6 * γ)) ^ 2 ≤ (2 * a + 3 * b + 6 * c_abs) ^ 2 := by
      rw [← sq_abs (Real.sin (2 * α + 3 * β - 6 * γ))]
      nlinarith [abs_nonneg (Real.sin (2 * α + 3 * β - 6 * γ)), abs_nonneg (Real.sin α),
        abs_nonneg (Real.sin β), abs_nonneg (Real.sin γ)]
    have h_cs : (2 * a + 3 * b + 6 * c_abs) ^ 2 ≤ 49 * (a ^ 2 + b ^ 2 + c_abs ^ 2) := by
      nlinarith [sq_nonneg (3 * a - 2 * b), sq_nonneg (6 * a - 2 * c_abs), sq_nonneg (6 * b - 3 * c_abs)]
    calc (Real.sin (2 * α + 3 * β - 6 * γ)) ^ 2
        ≤ (2 * a + 3 * b + 6 * c_abs) ^ 2 := h_sq1
      _ ≤ 49 * (a ^ 2 + b ^ 2 + c_abs ^ 2) := h_cs
      _ = 49 * ((Real.sin α) ^ 2 + (Real.sin β) ^ 2 + (Real.sin γ) ^ 2) := by
          simp only [a, b, c_abs, sq_abs]

  
  have h_s2 : ∀ (m N : ℕ),
      ∑ j ∈ Finset.range N,
        (Real.sin (Real.pi * (c ((2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))) : ℝ) /
          (((2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1)) : ℕ) : ℝ))) ^ 2 ≤ 49 * M := by
    intro m N
    let m_val : ℕ → ℕ := fun j => (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))
    have hm_pos : ∀ j : ℕ, 0 < m_val j := fun j => by dsimp [m_val]; positivity
    let D_N : ℕ := 7135 * m_val N
    have hDN_pos : 0 < D_N := Nat.mul_pos (by omega) (hm_pos N)
    let g : ℕ → ℝ := fun r =>
      (Real.sin (Real.pi * (c D_N : ℝ) * (1189 * (w_Icc (J r).1 (J r).2 : ℝ)))) ^ 2
    let f : Fin (l_seq D_N) → ℝ := fun i =>
      (Real.sin (Real.pi * (c D_N : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2
    have h_j_bound : ∀ j ∈ Finset.range N,
        (Real.sin (Real.pi * (c (m_val j) : ℝ) / ((m_val j : ℕ) : ℝ))) ^ 2 ≤
          49 * (g (3 * p_idx m j) + g (3 * p_idx m j + 1) + g (3 * p_idx m j + 2)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have h_dvd_mN : m_val j ∣ m_val N := by
        dsimp [m_val]
        apply mul_dvd_mul_left (2 * m + 1)
        apply Nat.pow_dvd_pow 2
        apply Nat.mul_le_mul_left
        omega
      have h_dvd_DN : m_val j ∣ D_N := dvd_mul_of_dvd_right h_dvd_mN 7135
      obtain ⟨k_j, hk_j⟩ := hc_compat (m_val j) D_N (hm_pos j) hDN_pos h_dvd_DN
      have hc_DN_eq : (c D_N : ℝ) = (c (m_val j) : ℝ) + (m_val j : ℝ) * (k_j : ℝ) := by
        have : c D_N = c (m_val j) + (m_val j : ℤ) * k_j := by omega
        exact_mod_cast this
      have h_sin_eq : (Real.sin (Real.pi * (c (m_val j) : ℝ) / ((m_val j : ℕ) : ℝ))) ^ 2 =
          (Real.sin (Real.pi * (c D_N : ℝ) / ((m_val j : ℕ) : ℝ))) ^ 2 := by
        have h_pos_r : (0 : ℝ) < (m_val j : ℝ) := Nat.cast_pos.mpr (hm_pos j)
        have h_arg : Real.pi * (c D_N : ℝ) / (m_val j : ℝ) =
            Real.pi * (c (m_val j) : ℝ) / (m_val j : ℝ) + (k_j : ℝ) * Real.pi := by
          rw [hc_DN_eq]
          field_simp [ne_of_gt h_pos_r]
        rw [h_arg, h_sin_add_int_mul_pi_sq]
      rw [h_sin_eq]
      have h_id_q : 2 * (1189 * w_Icc (J (3 * p_idx m j)).1 (J (3 * p_idx m j)).2) +
          3 * (1189 * w_Icc (J (3 * p_idx m j + 1)).1 (J (3 * p_idx m j + 1)).2) -
          6 * (1189 * w_Icc (J (3 * p_idx m j + 2)).1 (J (3 * p_idx m j + 2)).2) =
          (m_val j : ℚ)⁻¹ := (hJ_ident m j).2.2.2
      have h_id_r : 2 * (1189 * (w_Icc (J (3 * p_idx m j)).1 (J (3 * p_idx m j)).2 : ℝ)) +
          3 * (1189 * (w_Icc (J (3 * p_idx m j + 1)).1 (J (3 * p_idx m j + 1)).2 : ℝ)) -
          6 * (1189 * (w_Icc (J (3 * p_idx m j + 2)).1 (J (3 * p_idx m j + 2)).2 : ℝ)) =
          ((m_val j : ℝ))⁻¹ := by
        have h_cast := congr_arg ((↑) : ℚ → ℝ) h_id_q
        simpa only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_inv,
          Rat.cast_natCast, Rat.cast_ofNat] using h_cast
      have h_arg2 : Real.pi * (c D_N : ℝ) / ((m_val j : ℕ) : ℝ) =
          2 * (Real.pi * (c D_N : ℝ) * (1189 * (w_Icc (J (3 * p_idx m j)).1 (J (3 * p_idx m j)).2 : ℝ))) +
          3 * (Real.pi * (c D_N : ℝ) * (1189 * (w_Icc (J (3 * p_idx m j + 1)).1 (J (3 * p_idx m j + 1)).2 : ℝ))) -
          6 * (Real.pi * (c D_N : ℝ) * (1189 * (w_Icc (J (3 * p_idx m j + 2)).1 (J (3 * p_idx m j + 2)).2 : ℝ))) := by
        rw [div_eq_mul_inv, ← h_id_r]
        ring
      rw [h_arg2]
      exact h_sin_two_three_six_sq _ _ _
    let S_of : ℕ → Finset ℕ := fun j => {3 * p_idx m j, 3 * p_idx m j + 1, 3 * p_idx m j + 2}
    have hS_sum : ∀ j : ℕ, ∑ r ∈ S_of j, g r =
        g (3 * p_idx m j) + g (3 * p_idx m j + 1) + g (3 * p_idx m j + 2) := by
      intro j
      dsimp [S_of]
      rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
      ring
    have hS_disj : (Finset.range N : Set ℕ).PairwiseDisjoint S_of := by
      intro j₁ hj₁ j₂ hj₂ hj_ne
      change Disjoint (S_of j₁) (S_of j₂)
      rw [Finset.disjoint_left]
      intro r hr₁ hr₂
      dsimp [S_of] at hr₁ hr₂
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr₁ hr₂
      have hp1 : r / 3 = p_idx m j₁ := by omega
      have hp2 : r / 3 = p_idx m j₂ := by omega
      have h_eq := (hp_inj m j₁ m j₂ (hp1.symm.trans hp2)).2
      exact hj_ne h_eq
    let R_set : Finset ℕ := (Finset.range N).biUnion S_of
    have h_sum_R : ∑ j ∈ Finset.range N,
        (g (3 * p_idx m j) + g (3 * p_idx m j + 1) + g (3 * p_idx m j + 2)) = ∑ r ∈ R_set, g r := by
      calc ∑ j ∈ Finset.range N, (g (3 * p_idx m j) + g (3 * p_idx m j + 1) + g (3 * p_idx m j + 2))
          = ∑ j ∈ Finset.range N, ∑ r ∈ S_of j, g r :=
            Finset.sum_congr rfl (fun j _ => (hS_sum j).symm)
        _ = ∑ r ∈ R_set, g r := (Finset.sum_biUnion hS_disj).symm
    have hR_le_DN : ∀ r ∈ R_set, (J r).2 ≤ D_N := by
      intro r hr
      rw [Finset.mem_biUnion] at hr
      obtain ⟨j, hj, hrS⟩ := hr
      rw [Finset.mem_range] at hj
      have h_mval_le : m_val j ≤ m_val N := by
        dsimp [m_val]
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by decide)
        apply Nat.mul_le_mul_left
        omega
      have h_7135_le : 7135 * m_val j ≤ D_N := Nat.mul_le_mul_left 7135 h_mval_le
      have h_id := hJ_ident m j
      dsimp [S_of] at hrS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrS
      rcases hrS with rfl | rfl | rfl
      · exact le_trans h_id.1 h_7135_le
      · exact le_trans h_id.2.1 h_7135_le
      · exact le_trans h_id.2.2.1 h_7135_le
    let idx_of : {r // r ∈ R_set} → Fin (l_seq D_N) :=
      fun r => Classical.choose (h_gadget_mem r.1 D_N (hR_le_DN r.1 r.2))
    have h_idx_spec : ∀ r : {r // r ∈ R_set}, I_seq (idx_of r).1 = J r.1 :=
      fun r => Classical.choose_spec (h_gadget_mem r.1 D_N (hR_le_DN r.1 r.2))
    have h_idx_inj : Function.Injective idx_of := by
      intro r₁ r₂ h_eq
      have hJ_eq : J r₁.1 = J r₂.1 := by
        rw [← h_idx_spec r₁, ← h_idx_spec r₂, h_eq]
      by_contra h_ne
      have h_val_ne : r₁.1 ≠ r₂.1 := fun h => h_ne (Subtype.ext h)
      have h_sep_r := hJ_sep r₁.1 r₂.1 h_val_ne
      have hb1 := (hJ_bounds r₁.1).2.1
      rw [hJ_eq] at h_sep_r hb1
      omega
    have h_sum_R_le : ∑ r ∈ R_set, g r ≤ ∑ i : Fin (l_seq D_N), f i := by
      rw [← Finset.sum_attach R_set g]
      have h_fg : ∀ r : {r // r ∈ R_set}, g r.1 = f (idx_of r) := by
        intro r
        dsimp [g, f]
        rw [h_idx_spec r]
      rw [Finset.sum_congr rfl (fun r _ => h_fg r)]
      rw [← Finset.sum_image (f := f) (fun x _ y _ hxy => h_idx_inj hxy)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have h_tot_sum := Finset.sum_le_sum h_j_bound
    rw [← Finset.mul_sum, h_sum_R] at h_tot_sum
    have h_en := hc_energy D_N D_N (le_refl D_N)
    linarith

  
  have h_s3 : ∀ (d₀ K : ℕ), 1 ≤ d₀ → 2 ≤ K →
      (∀ j : ℕ, ((d₀ * K ^ j : ℕ) : ℤ) ∣ (c (d₀ * K ^ (j + 1)) - c (d₀ * K ^ j))) →
      (∀ N : ℕ, ∑ j ∈ Finset.range N,
        (Real.sin (Real.pi * (c (d₀ * K ^ j) : ℝ) / ((d₀ * K ^ j : ℕ) : ℝ))) ^ 2 ≤ 49 * M) →
      ∃ a : ℤ, ∀ j : ℕ, ((d₀ * K ^ j : ℕ) : ℤ) ∣ (c (d₀ * K ^ j) - a) := by
    intro d₀ K hd₀ hK hc_step hc_sum
    let B_sum : ℝ := 49 * M
    let M_nat : ℕ → ℕ := fun j => d₀ * K ^ j
    have hM_pos : ∀ j : ℕ, 0 < M_nat j := fun j => Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    have hM_pos_r : ∀ j : ℕ, (0 : ℝ) < (M_nat j : ℝ) := fun j => Nat.cast_pos.mpr (hM_pos j)
    let q_of : ℕ → ℤ := fun j => ⌊(c (M_nat j) : ℝ) / (M_nat j : ℝ) + 1 / 2⌋
    let z_of : ℕ → ℤ := fun j => c (M_nat j) - q_of j * (M_nat j : ℤ)
    let δ_of : ℕ → ℝ := fun j => (z_of j : ℝ) / (M_nat j : ℝ)
    have hδ_eq : ∀ j : ℕ, δ_of j = (c (M_nat j) : ℝ) / (M_nat j : ℝ) - (q_of j : ℝ) := by
      intro j
      dsimp [δ_of, z_of]
      push_cast
      have := ne_of_gt (hM_pos_r j)
      field_simp
    have hδ_bounds : ∀ j : ℕ, -(1 / 2) ≤ δ_of j ∧ δ_of j ≤ 1 / 2 := by
      intro j
      rw [hδ_eq j]
      have h1 := Int.floor_le ((c (M_nat j) : ℝ) / (M_nat j : ℝ) + 1 / 2)
      have h2 := Int.lt_floor_add_one ((c (M_nat j) : ℝ) / (M_nat j : ℝ) + 1 / 2)
      constructor <;> linarith
    have h_term_bound : ∀ j : ℕ,
        4 * (δ_of j) ^ 2 ≤ (Real.sin (Real.pi * (c (M_nat j) : ℝ) / (M_nat j : ℝ))) ^ 2 := by
      intro j
      have h_arg : Real.pi * (c (M_nat j) : ℝ) / (M_nat j : ℝ) =
          Real.pi * δ_of j + (q_of j : ℝ) * Real.pi := by
        rw [hδ_eq j]
        ring
      rw [h_arg, h_sin_add_int_mul_pi_sq]
      exact h_jordan_sin_sq_bound (δ_of j) (hδ_bounds j).1 (hδ_bounds j).2
    have h_sum_δ : ∀ N : ℕ, ∑ j ∈ Finset.range N, (δ_of j) ^ 2 ≤ B_sum / 4 := by
      intro N
      have h1 : 4 * ∑ j ∈ Finset.range N, (δ_of j) ^ 2 ≤
          ∑ j ∈ Finset.range N, (Real.sin (Real.pi * (c (M_nat j) : ℝ) / (M_nat j : ℝ))) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j _ => h_term_bound j)
      have h2 := hc_sum N
      linarith
    set η : ℝ := 1 / (9 * (K : ℝ) ^ 2)
    have hK_pos_r : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hK_ge1_r : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
    have hη_pos : 0 < η := by positivity
    have h_tail : ∃ J₀ : ℕ, ∀ j ≥ J₀, (δ_of j) ^ 2 < η := by
      by_contra! h_not
      have h_ind : ∀ m : ℕ, ∃ N : ℕ, (m : ℝ) * η ≤ ∑ j ∈ Finset.range N, (δ_of j) ^ 2 := by
        intro m
        induction m with
        | zero => exact ⟨0, by simp⟩
        | succ m ih =>
          obtain ⟨N, hN⟩ := ih
          obtain ⟨j, hj_ge, hj_eta⟩ := h_not N
          refine ⟨j + 1, ?_⟩
          have h_mono_sum : ∑ k ∈ Finset.range N, (δ_of k) ^ 2 ≤ ∑ k ∈ Finset.range j, (δ_of k) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj_ge) (fun _ _ _ => sq_nonneg _)
          rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
          linarith
      let m₀ : ℕ := Nat.floor (B_sum / (4 * η)) + 1
      obtain ⟨N₀, hN₀⟩ := h_ind m₀
      have h_ub := h_sum_δ N₀
      have h_lt : B_sum / (4 * η) < (m₀ : ℝ) := by
        dsimp [m₀]
        push_cast
        exact Nat.lt_floor_add_one (B_sum / (4 * η))
      have h_mul_lt : B_sum / 4 < (m₀ : ℝ) * η := by
        have h_pos4 : 0 < 4 * η := by positivity
        have := (div_lt_iff₀ h_pos4).mp h_lt
        linarith
      linarith
    obtain ⟨J₀, hJ₀⟩ := h_tail
    have hδ_abs : ∀ j ≥ J₀, |δ_of j| < 1 / (3 * (K : ℝ)) := by
      intro j hj
      have hsq := hJ₀ j hj
      have h_pos3K : 0 < 1 / (3 * (K : ℝ)) := by positivity
      by_contra! h_ge
      have h_sq_ge : (1 / (3 * (K : ℝ))) ^ 2 ≤ |δ_of j| ^ 2 := by nlinarith
      rw [sq_abs] at h_sq_ge
      have h_eq : (1 / (3 * (K : ℝ))) ^ 2 = η := by dsimp [η]; ring
      linarith
    have hz_step : ∀ j ≥ J₀, z_of (j + 1) = z_of j := by
      intro j hj
      have hM_succ : M_nat (j + 1) = M_nat j * K := by
        dsimp [M_nat]
        rw [Nat.pow_succ]
        ring
      have h_dvd_diff : (M_nat j : ℤ) ∣ (z_of (j + 1) - z_of j) := by
        dsimp [z_of]
        rw [hM_succ]
        push_cast
        have h_step_j : (M_nat j : ℤ) ∣ (c (M_nat j * K) - c (M_nat j)) := by
          rw [← hM_succ]
          exact hc_step j
        have h_id : c (M_nat j * K) - q_of (j + 1) * ((M_nat j : ℤ) * (K : ℤ)) -
            (c (M_nat j) - q_of j * (M_nat j : ℤ)) =
            (c (M_nat j * K) - c (M_nat j)) -
            (M_nat j : ℤ) * (q_of (j + 1) * (K : ℤ) - q_of j) := by ring
        rw [h_id]
        exact dvd_sub h_step_j (dvd_mul_right (M_nat j : ℤ) _)
      have h_lt_abs : |z_of (j + 1) - z_of j| < (M_nat j : ℤ) := by
        have hz_r : ∀ k : ℕ, (z_of k : ℝ) = δ_of k * (M_nat k : ℝ) := by
          intro k
          dsimp [δ_of]
          exact (div_mul_cancel₀ (z_of k : ℝ) (ne_of_gt (hM_pos_r k))).symm
        have h_abs1 := hδ_abs j hj
        have h_abs2 := hδ_abs (j + 1) (by omega)
        have h_abs_z1 : |(z_of j : ℝ)| < (1 / 3 : ℝ) * (M_nat j : ℝ) := by
          rw [hz_r j, abs_mul, abs_of_pos (hM_pos_r j)]
          have h_3K : 1 / (3 * (K : ℝ)) ≤ 1 / 3 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
          nlinarith [hM_pos_r j]
        have h_abs_z2 : |(z_of (j + 1) : ℝ)| < (1 / 3 : ℝ) * (M_nat j : ℝ) := by
          rw [hz_r (j + 1), hM_succ, Nat.cast_mul, abs_mul, abs_mul,
            abs_of_pos (hM_pos_r j), abs_of_pos hK_pos_r]
          have h_mul_K : |δ_of (j + 1)| * (K : ℝ) < 1 / 3 := by
            have := mul_lt_mul_of_pos_right h_abs2 hK_pos_r
            have h_eq : 1 / (3 * (K : ℝ)) * (K : ℝ) = 1 / 3 := by field_simp [ne_of_gt hK_pos_r]
            rwa [h_eq] at this
          nlinarith [hM_pos_r j]
        have h_diff_r : |((z_of (j + 1) - z_of j : ℤ) : ℝ)| < (M_nat j : ℝ) := by
          push_cast
          have h_tri := abs_sub (z_of (j + 1) : ℝ) (z_of j : ℝ)
          linarith
        exact_mod_cast h_diff_r
      have h_zero := Int.eq_zero_of_abs_lt_dvd h_dvd_diff h_lt_abs
      exact sub_eq_zero.mp h_zero
    let a : ℤ := z_of J₀
    have hz_eq_a : ∀ k : ℕ, z_of (J₀ + k) = a := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← Nat.add_assoc, hz_step (J₀ + k) (by omega), ih]
    have h_diff_k : ∀ j k : ℕ, (M_nat j : ℤ) ∣ (c (M_nat (j + k)) - c (M_nat j)) := by
      intro j k
      induction k with
      | zero => simp
      | succ k ih =>
        have h_id : c (M_nat (j + (k + 1))) - c (M_nat j) =
            (c (M_nat (j + k + 1)) - c (M_nat (j + k))) + (c (M_nat (j + k)) - c (M_nat j)) := by
          rw [← Nat.add_assoc]
          ring
        rw [h_id]
        have h_dvd_M : (M_nat j : ℤ) ∣ (M_nat (j + k) : ℤ) := by
          have : M_nat j ∣ M_nat (j + k) := by
            dsimp [M_nat]
            exact mul_dvd_mul_left d₀ (Nat.pow_dvd_pow K (by omega))
          exact_mod_cast this
        exact dvd_add (dvd_trans h_dvd_M (hc_step (j + k))) ih
    refine ⟨a, fun j => ?_⟩
    have h_dvd_M_N : (M_nat j : ℤ) ∣ (M_nat (J₀ + j) : ℤ) := by
      have : M_nat j ∣ M_nat (J₀ + j) := by
        dsimp [M_nat]
        exact mul_dvd_mul_left d₀ (Nat.pow_dvd_pow K (by omega))
      exact_mod_cast this
    have h1 : (M_nat j : ℤ) ∣ (c (M_nat (J₀ + j)) - a) := by
      rw [← hz_eq_a j]
      have h_eq : c (M_nat (J₀ + j)) - z_of (J₀ + j) = (M_nat (J₀ + j) : ℤ) * q_of (J₀ + j) := by
        dsimp [z_of]
        ring
      rw [h_eq]
      exact dvd_trans h_dvd_M_N (dvd_mul_right _ _)
    have h2 : (M_nat j : ℤ) ∣ (c (M_nat (J₀ + j)) - c (M_nat j)) := by
      rw [Nat.add_comm J₀ j]
      exact h_diff_k j J₀
    have h_id : c (M_nat j) - a = (c (M_nat (J₀ + j)) - a) - (c (M_nat (J₀ + j)) - c (M_nat j)) := by ring
    rw [h_id]
    exact dvd_sub h1 h2

  
  have h_chain : ∀ m : ℕ, ∃ a_m : ℤ, ∀ j : ℕ,
      (((2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1)) : ℕ) : ℤ) ∣
        (c ((2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))) - a_m) := by
    intro m
    let d₀ : ℕ := (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m)
    let K : ℕ := 2 ^ (120 * (B + 2) * 2 ^ m)
    have hd₀ : 1 ≤ d₀ := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    have hK : 2 ≤ K := by
      have h_exp : 1 ≤ 120 * (B + 2) * 2 ^ m := Nat.mul_pos (by omega) (Nat.two_pow_pos m)
      exact le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) h_exp)
    have h_mval_eq : ∀ j : ℕ, d₀ * K ^ j = (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1)) := by
      intro j
      dsimp [d₀, K]
      rw [mul_assoc, ← Nat.pow_mul, ← Nat.pow_add]
      congr 2
      ring
    have hc_step_m : ∀ j : ℕ, ((d₀ * K ^ j : ℕ) : ℤ) ∣ (c (d₀ * K ^ (j + 1)) - c (d₀ * K ^ j)) := by
      intro j
      have h_pos1 : 0 < d₀ * K ^ j := Nat.mul_pos hd₀ (Nat.pow_pos (by omega))
      have h_pos2 : 0 < d₀ * K ^ (j + 1) := Nat.mul_pos hd₀ (Nat.pow_pos (by omega))
      have h_dvd : d₀ * K ^ j ∣ d₀ * K ^ (j + 1) :=
        mul_dvd_mul_left d₀ (Nat.pow_dvd_pow K (by omega))
      exact hc_compat (d₀ * K ^ j) (d₀ * K ^ (j + 1)) h_pos1 h_pos2 h_dvd
    have hc_sum_m : ∀ N : ℕ, ∑ j ∈ Finset.range N,
        (Real.sin (Real.pi * (c (d₀ * K ^ j) : ℝ) / ((d₀ * K ^ j : ℕ) : ℝ))) ^ 2 ≤ 49 * M := by
      intro N
      simp_rw [h_mval_eq]
      exact h_s2 m N
    obtain ⟨a_m, ha_m⟩ := h_s3 d₀ K hd₀ hK hc_step_m hc_sum_m
    refine ⟨a_m, fun j => ?_⟩
    rw [← h_mval_eq j]
    exact ha_m j

  
  let m_val_all : ℕ → ℕ → ℕ := fun m j => (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))
  have hm_pos_all : ∀ m j : ℕ, 0 < m_val_all m j := fun m j => by dsimp [m_val_all]; positivity
  let a_of : ℕ → ℤ := fun m => Classical.choose (h_chain m)
  have ha_of : ∀ m j : ℕ, ((m_val_all m j : ℕ) : ℤ) ∣ (c (m_val_all m j) - a_of m) :=
    fun m => Classical.choose_spec (h_chain m)
  let a_star : ℤ := a_of 0
  have h_lin_id : ∀ x y z w : ℤ, z - w = (x - y) - (x - z) + (y - w) := by intro x y z w; ring
  have ha_eq : ∀ m : ℕ, a_of m = a_star := by
    intro m
    let j : ℕ := (a_of m - a_star).natAbs
    have h_dvd_nat : m_val_all 0 j ∣ m_val_all m j := by
      change (2 * 0 + 1) * 2 ^ (60 * (B + 2) * 2 ^ 0 * (2 * j + 1)) ∣
        (2 * m + 1) * 2 ^ (60 * (B + 2) * 2 ^ m * (2 * j + 1))
      rw [Nat.mul_zero, Nat.zero_add, Nat.pow_zero, one_mul]
      have h_exp : 60 * (B + 2) * 1 * (2 * j + 1) ≤ 60 * (B + 2) * 2 ^ m * (2 * j + 1) := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact Nat.one_le_two_pow
      exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 h_exp) (2 * m + 1)
    have h_dvd_z : ((m_val_all 0 j : ℕ) : ℤ) ∣ ((m_val_all m j : ℕ) : ℤ) := by exact_mod_cast h_dvd_nat
    have h1 : ((m_val_all 0 j : ℕ) : ℤ) ∣ (c (m_val_all m j) - c (m_val_all 0 j)) :=
      hc_compat (m_val_all 0 j) (m_val_all m j) (hm_pos_all 0 j) (hm_pos_all m j) h_dvd_nat
    have h2 : ((m_val_all 0 j : ℕ) : ℤ) ∣ (c (m_val_all m j) - a_of m) :=
      dvd_trans h_dvd_z (ha_of m j)
    have h3 : ((m_val_all 0 j : ℕ) : ℤ) ∣ (c (m_val_all 0 j) - a_star) :=
      ha_of 0 j
    have h_diff_dvd : ((m_val_all 0 j : ℕ) : ℤ) ∣ (a_of m - a_star) := by
      rw [h_lin_id (c (m_val_all m j)) (c (m_val_all 0 j)) (a_of m) a_star]
      exact dvd_add (dvd_sub h1 h2) h3
    have h_lt : |a_of m - a_star| < ((m_val_all 0 j : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      have h_j_lt : j < m_val_all 0 j := by
        change j < (2 * 0 + 1) * 2 ^ (60 * (B + 2) * 2 ^ 0 * (2 * j + 1))
        rw [Nat.mul_zero, Nat.zero_add, Nat.pow_zero, one_mul, mul_one]
        have h_pow1 : j < 2 ^ j := Nat.lt_two_pow_self
        have h_exp : j ≤ 60 * (B + 2) * (2 * j + 1) := by
          have := Nat.mul_le_mul_right (2 * j + 1) (by omega : 1 ≤ 60 * (B + 2))
          omega
        have h_pow2 : 2 ^ j ≤ 2 ^ (60 * (B + 2) * (2 * j + 1)) := Nat.pow_le_pow_right (by decide) h_exp
        exact lt_of_lt_of_le h_pow1 h_pow2
      exact_mod_cast h_j_lt
    have h_zero : a_of m - a_star = 0 := Int.eq_zero_of_abs_lt_dvd h_diff_dvd h_lt
    exact sub_eq_zero.mp h_zero
  have h_dyadic : ∀ d : ℕ, 0 < d → ∃ m v : ℕ, d = (2 * m + 1) * 2 ^ v := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd
      rcases Nat.even_or_odd' d with ⟨k, rfl | rfl⟩
      · have hk_pos : 0 < k := by omega
        have hk_lt : k < 2 * k := by omega
        obtain ⟨m, v, hmv⟩ := ih k hk_lt hk_pos
        refine ⟨m, v + 1, ?_⟩
        rw [hmv, Nat.pow_succ]
        ring
      · exact ⟨k, 0, by ring⟩
  have ha_star_div : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (c d - a_star) := by
    intro d hd
    obtain ⟨m, v, rfl⟩ := h_dyadic d hd
    have h_dvd_mval : (2 * m + 1) * 2 ^ v ∣ m_val_all m v := by
      dsimp [m_val_all]
      apply mul_dvd_mul_left (2 * m + 1)
      apply Nat.pow_dvd_pow 2
      have h1 : 1 ≤ 60 * (B + 2) * 2 ^ m := Nat.mul_pos (by omega) (Nat.two_pow_pos m)
      have h2 : 1 * (2 * v + 1) ≤ (60 * (B + 2) * 2 ^ m) * (2 * v + 1) :=
        Nat.mul_le_mul_right (2 * v + 1) h1
      omega
    have hd_z_dvd : (((2 * m + 1) * 2 ^ v : ℕ) : ℤ) ∣ ((m_val_all m v : ℕ) : ℤ) := by exact_mod_cast h_dvd_mval
    have h_c1 : (((2 * m + 1) * 2 ^ v : ℕ) : ℤ) ∣ (c (m_val_all m v) - c ((2 * m + 1) * 2 ^ v)) :=
      hc_compat ((2 * m + 1) * 2 ^ v) (m_val_all m v) hd (hm_pos_all m v) h_dvd_mval
    have h_c2 : (((2 * m + 1) * 2 ^ v : ℕ) : ℤ) ∣ (c (m_val_all m v) - a_star) := by
      rw [← ha_eq m]
      exact dvd_trans hd_z_dvd (ha_of m v)
    have h_sub_id : ∀ x y z : ℤ, y - z = (x - z) - (x - y) := by intro x y z; ring
    rw [h_sub_id (c (m_val_all m v)) (c ((2 * m + 1) * 2 ^ v)) a_star]
    exact dvd_sub h_c2 h_c1

  
  refine ⟨a_star, ha_star_div, fun Y hY => ?_⟩
  let D : ℕ := (Finset.Icc 1 Y).lcm id
  have hD_pos : 0 < D := by
    refine Nat.pos_of_ne_zero ?_
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    intro ⟨x, hx, hx0⟩
    rw [Finset.mem_Icc] at hx
    simp only [id_eq] at hx0
    omega
  let d : ℕ := Y * D
  have hd_pos : 0 < d := Nat.mul_pos (by omega) hD_pos
  have hY_le_d : Y ≤ d := Nat.le_mul_of_pos_right Y hD_pos
  have hD_dvd_diff : (D : ℤ) ∣ (c d - a_star) := by
    have hD_dvd_d : (D : ℤ) ∣ (d : ℤ) := dvd_mul_left (D : ℤ) (Y : ℤ)
    exact dvd_trans hD_dvd_d (ha_star_div d hd_pos)
  obtain ⟨k_d, hk_d⟩ := hD_dvd_diff
  have hc_d_eq : (c d : ℝ) = (a_star : ℝ) + (D : ℝ) * (k_d : ℝ) := by
    have : c d = a_star + (D : ℤ) * k_d := by omega
    exact_mod_cast this
  have h_term_eq : ∀ i : Fin (l_seq Y),
      (Real.sin (Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 =
      (Real.sin (Real.pi * (c d : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 := by
    intro i
    let q_i : ℚ := (D : ℚ) * w_Icc (I_seq i.1).1 (I_seq i.1).2
    have hq_den : q_i.den = 1 := (h_scale_lcm Y hY).2 i
    have hq_int : (q_i : ℝ) = (q_i.num : ℝ) := by
      have : q_i = (q_i.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hq_den).symm
      exact_mod_cast this
    have hD_w : (D : ℝ) * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ) = (q_i.num : ℝ) := by
      have h_cast : (q_i : ℝ) = (D : ℝ) * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ) := by
        dsimp [q_i]
        push_cast
        rfl
      linarith
    have h_arg : Real.pi * (c d : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) =
        Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) +
        (((k_d * 1189 * q_i.num : ℤ) : ℝ) * Real.pi) := by
      rw [hc_d_eq]
      push_cast
      calc Real.pi * ((a_star : ℝ) + (D : ℝ) * (k_d : ℝ)) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ))
          = Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) +
            (k_d : ℝ) * 1189 * ((D : ℝ) * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) * Real.pi := by ring
        _ = Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) +
            (k_d : ℝ) * 1189 * (q_i.num : ℝ) * Real.pi := by rw [hD_w]
    rw [h_arg, h_sin_add_int_mul_pi_sq]
  rw [Finset.sum_congr rfl (fun i _ => h_term_eq i)]
  exact hc_energy Y d hY_le_d

theorem lacunary_rigidity_and_combined_reserve_merge (B : ℕ) (l_dig : ℕ → ℕ) (I_dig : ℕ → ℕ × ℕ)
    (hB : 1189 ≤ B)
    (h_dig_bounds : ∀ k : ℕ, 495 ≤ (I_dig k).1 ∧ (I_dig k).1 < (I_dig k).2 ∧ (I_dig k).2 ≤ (I_dig k).1 + 2)
    (h_dig_sep : ∀ k m : ℕ, k ≠ m → (I_dig k).2 + 1 < (I_dig m).1 ∨ (I_dig m).2 + 1 < (I_dig k).1)
    (h_dig_mono : 1 ≤ l_dig B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_dig Y₁ ≤ l_dig Y₂)
    (h_dig_mass : ∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_dig k).1 (I_dig k).2 ≤ 1 / 237800)
    (h_dig_scale : ∀ Y ≥ B, l_dig Y ≤ 2 ^ 56 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
      ∀ i : Fin (l_dig Y), (I_dig i.1).2 ≤ Y ^ 2 / 2 ∧
        ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_dig i.1).1 (I_dig i.1).2).den = 1)
    (h_dig_energy : ∀ q : ℕ, B < q → ∀ δ : ℤ,
      ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
      ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
      16 * Real.log (q : ℝ) ≤
        ∑ k ∈ (Finset.range (l_dig q)) \ (Finset.range (l_dig (q - 1))),
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_dig k).1 (I_dig k).2 : ℝ)))) ^ 2) :
    ∃ (l_seq : ℕ → ℕ) (I_seq : ℕ → ℕ × ℕ),
      (∀ k : ℕ, 495 ≤ (I_seq k).1 ∧ (I_seq k).1 < (I_seq k).2 ∧ (I_seq k).2 ≤ (I_seq k).1 + 2) ∧
      (∀ k m : ℕ, k ≠ m → (I_seq k).2 + 1 < (I_seq m).1 ∨ (I_seq m).2 + 1 < (I_seq k).1) ∧
      (1 ≤ l_seq B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_seq Y₁ ≤ l_seq Y₂) ∧
      (∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_seq k).1 (I_seq k).2 ≤ 1 / 118900) ∧
      (∀ Y ≥ B, l_seq Y ≤ 2 ^ 57 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
        ∀ i : Fin (l_seq Y), ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_seq i.1).1 (I_seq i.1).2).den = 1) ∧
      (∀ q : ℕ, B < q → ∀ δ : ℤ,
        ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
        ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
        12 * Real.log (q : ℝ) ≤
          ∑ k ∈ (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))),
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)))) ^ 2) ∧
      (∀ (M : ℝ), 0 < M →
        ∀ (Y_seq : ℕ → ℕ) (a_seq : ℕ → ℤ),
          (∀ j : ℕ, B + j ≤ Y_seq j ∧
            ∑ i : Fin (l_seq (Y_seq j)),
              (Real.sin (Real.pi * (a_seq j : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ M) →
          ∃ a_star : ℤ,
            (∀ Y ≥ B, ∑ i : Fin (l_seq Y),
              (Real.sin (Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ M) ∧
            (∀ Q ≥ B, ∃ j : ℕ, Q ≤ j ∧
              ((((Finset.Icc 1 Q).lcm id) / 1189 : ℕ) : ℤ) ∣ (a_seq j - a_star))) :=
by
  classical
  obtain ⟨J, p_idx, hJ_bounds, hJ_sep, hJ_growth, hJ_mass, hp_inj, hJ_ident⟩ :=
    universal_lacunary_gadget_sequence_existence B hB
  obtain ⟨l_seq, I_seq, h_bounds, h_sep, h_mono, h_mass, h_scale_lcm, h_step_energy, h_gadget_mem⟩ :=
    pruned_digit_and_gadget_reserve_merge B l_dig I_dig hB h_dig_bounds h_dig_sep h_dig_mono
      h_dig_mass h_dig_scale h_dig_energy J hJ_bounds hJ_sep hJ_growth hJ_mass
  refine ⟨l_seq, I_seq, h_bounds, h_sep, h_mono, h_mass, h_scale_lcm, h_step_energy, ?_⟩
  intro M hM Y_seq a_seq h_seq
  have h_inf_fiber : ∀ (S : Set ℕ), S.Infinite → ∀ (K : ℕ), 0 < K →
      ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧ ∀ x ∈ T, ∀ y ∈ T, (K : ℤ) ∣ (a_seq x - a_seq y) := by
    intro S hS K hK
    haveI : Infinite S := hS.to_subtype
    haveI : NeZero K := ⟨Nat.ne_of_gt hK⟩
    let f : S → ZMod K := fun x => (a_seq x.1 : ZMod K)
    obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber f
    let T : Set ℕ := {n ∈ S | (a_seq n : ZMod K) = r}
    refine ⟨T, fun n hn => hn.1, ?_, ?_⟩
    · have h_eq : T = Subtype.val '' (f ⁻¹' {r}) := by
        ext n
        simp only [T, f, Set.mem_setOf_eq, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff, Subtype.exists]
        exact ⟨fun ⟨hnS, hnr⟩ => ⟨n, hnS, hnr, rfl⟩, fun ⟨m, hmS, hmr, hmn⟩ => hmn ▸ ⟨hmS, hmr⟩⟩
      rw [h_eq]
      exact (Set.infinite_coe_iff.mp hr).image Subtype.val_injective.injOn
    · intro x hx y hy
      have h_eq : ((a_seq x - a_seq y : ℤ) : ZMod K) = 0 := by
        push_cast
        rw [hx.2, hy.2, sub_self]
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_eq
  let step : ℕ → {S : Set ℕ // S.Infinite} → {S : Set ℕ // S.Infinite} := fun d S =>
    let h := h_inf_fiber S.1 S.2 (Nat.factorial (d + 1)) (Nat.factorial_pos (d + 1))
    ⟨Classical.choose h, (Classical.choose_spec h).2.1⟩
  let chain : ℕ → {S : Set ℕ // S.Infinite} := fun d =>
    Nat.rec ⟨Set.univ, Set.infinite_univ⟩ step d
  have h_sub_succ : ∀ d : ℕ, (chain (d + 1)).1 ⊆ (chain d).1 := by
    intro d
    exact (Classical.choose_spec (h_inf_fiber (chain d).1 (chain d).2 (Nat.factorial (d + 1)) (Nat.factorial_pos (d + 1)))).1
  have h_mod_succ : ∀ d : ℕ, ∀ x ∈ (chain (d + 1)).1, ∀ y ∈ (chain (d + 1)).1,
      ((Nat.factorial (d + 1) : ℕ) : ℤ) ∣ (a_seq x - a_seq y) := by
    intro d
    exact (Classical.choose_spec (h_inf_fiber (chain d).1 (chain d).2 (Nat.factorial (d + 1)) (Nat.factorial_pos (d + 1)))).2.2
  have h_sub_le : ∀ d₁ d₂ : ℕ, d₁ ≤ d₂ → (chain d₂).1 ⊆ (chain d₁).1 := by
    intro d₁ d₂ hle
    induction hle with
    | refl => exact Set.Subset.rfl
    | @step m _ ih => exact Set.Subset.trans (h_sub_succ m) ih
  have h_ex_j : ∀ d : ℕ, ∃ j ∈ (chain d).1, d ≤ j := by
    intro d
    obtain ⟨j, hjS, hj_not_mem⟩ := (chain d).2.exists_notMem_finset (Finset.range d)
    rw [Finset.mem_range, not_lt] at hj_not_mem
    exact ⟨j, hjS, hj_not_mem⟩
  let j_of : ℕ → ℕ := fun d => Classical.choose (h_ex_j d)
  have hj_mem : ∀ d : ℕ, j_of d ∈ (chain d).1 := fun d => (Classical.choose_spec (h_ex_j d)).1
  have hj_ge : ∀ d : ℕ, d ≤ j_of d := fun d => (Classical.choose_spec (h_ex_j d)).2
  let c : ℕ → ℤ := fun d => a_seq (j_of d)
  have hc_compat : ∀ d₁ d₂ : ℕ, 0 < d₁ → 0 < d₂ → d₁ ∣ d₂ → (d₁ : ℤ) ∣ (c d₂ - c d₁) := by
    intro d₁ d₂ hd₁ hd₂ hdvd
    have hle : d₁ ≤ d₂ := Nat.le_of_dvd hd₂ hdvd
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd₁)
    have h_j2_in : j_of d₂ ∈ (chain (k + 1)).1 := h_sub_le (k + 1) d₂ hle (hj_mem d₂)
    have h_j1_in : j_of (k + 1) ∈ (chain (k + 1)).1 := hj_mem (k + 1)
    have h_fact_dvd : ((Nat.factorial (k + 1) : ℕ) : ℤ) ∣ (c d₂ - c (k + 1)) :=
      h_mod_succ k (j_of d₂) h_j2_in (j_of (k + 1)) h_j1_in
    have h_self_dvd_fact : ((k + 1 : ℕ) : ℤ) ∣ ((Nat.factorial (k + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (by omega) (le_refl (k + 1))
    exact dvd_trans h_self_dvd_fact h_fact_dvd
  have hc_energy : ∀ Y d : ℕ, Y ≤ d →
      ∑ i : Fin (l_seq Y),
        (Real.sin (Real.pi * (c d : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ M := by
    intro Y d hYd
    have hY_le_Yseq : Y ≤ Y_seq (j_of d) := by
      have h1 := hj_ge d
      have h2 := (h_seq (j_of d)).1
      omega
    have hl_le : l_seq Y ≤ l_seq (Y_seq (j_of d)) := h_mono.2 Y (Y_seq (j_of d)) hY_le_Yseq
    have h_sum_le : ∑ i : Fin (l_seq Y),
        (Real.sin (Real.pi * (c d : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤
        ∑ i : Fin (l_seq (Y_seq (j_of d))),
          (Real.sin (Real.pi * (a_seq (j_of d) : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => (Real.sin (Real.pi * (c d : ℝ) * (1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)))) ^ 2) (l_seq Y)]
      rw [Fin.sum_univ_eq_sum_range (fun k => (Real.sin (Real.pi * (a_seq (j_of d) : ℝ) * (1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)))) ^ 2) (l_seq (Y_seq (j_of d)))]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hl_le) ?_
      intro k _ _
      exact sq_nonneg _
    exact le_trans h_sum_le (h_seq (j_of d)).2
  obtain ⟨a_star, ha_star_div_all, ha_star_energy⟩ :=
    lacunary_gadget_integer_rigidity_lock B hB l_seq I_seq h_bounds h_sep h_mono h_scale_lcm
      J p_idx hJ_bounds hJ_sep hp_inj hJ_ident h_gadget_mem M hM c hc_compat hc_energy
  refine ⟨a_star, ha_star_energy, fun Q hQ => ?_⟩
  set L_Q : ℕ := ((Finset.Icc 1 Q).lcm id) / 1189
  have hD_pos : 0 < (Finset.Icc 1 Q).lcm id := by
    refine Nat.pos_of_ne_zero ?_
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    intro ⟨x, hx, hx0⟩
    rw [Finset.mem_Icc] at hx
    simp only [id_eq] at hx0
    omega
  have h1189_mem : 1189 ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨by omega, le_trans hB hQ⟩
  have h1189_dvd : 1189 ∣ (Finset.Icc 1 Q).lcm id := Finset.dvd_lcm h1189_mem
  have h1189_le_D : 1189 ≤ (Finset.Icc 1 Q).lcm id := Nat.le_of_dvd hD_pos h1189_dvd
  have hLQ_pos : 0 < L_Q := by
    dsimp [L_Q]
    omega
  set d : ℕ := Q * L_Q
  have hd_pos : 0 < d := Nat.mul_pos (by omega) hLQ_pos
  have hQ_le_d : Q ≤ d := Nat.le_mul_of_pos_right Q hLQ_pos
  refine ⟨j_of d, le_trans hQ_le_d (hj_ge d), ?_⟩
  have hLQ_dvd_d : (L_Q : ℤ) ∣ (d : ℤ) := by
    dsimp [d]
    exact dvd_mul_left (L_Q : ℤ) (Q : ℤ)
  have hd_dvd_diff : (d : ℤ) ∣ (c d - a_star) := ha_star_div_all d hd_pos
  exact dvd_trans hLQ_dvd_d hd_dvd_diff

theorem complete_period_gaussian_sine_kernel_bound (B : ℕ) (l_seq : ℕ → ℕ) (I_seq : ℕ → ℕ × ℕ)
    (hB : 1189 ≤ B)
    (h_mono : 1 ≤ l_seq B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_seq Y₁ ≤ l_seq Y₂)
    (h_den : ∀ Y ≥ B, ∀ i : Fin (l_seq Y),
      ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_seq i.1).1 (I_seq i.1).2).den = 1)
    (h_step_energy : ∀ q : ℕ, B < q → ∀ δ : ℤ,
      ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ →
      ¬ (((((Finset.Icc 1 q).lcm id) / 1189 : ℕ) : ℤ) ∣ δ) →
      12 * Real.log (q : ℝ) ≤
        ∑ k ∈ (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))),
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)))) ^ 2) :
    ∃ (C_m : ℚ), 0 < C_m ∧
      ∀ Y ≥ B,
        ∑ a ∈ Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2) ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1),
          Real.exp (- (1 / 3 : ℝ) * ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2) ≤ (C_m : ℝ) :=
by
  have h_lcm_props :
      (0 < ((Finset.Icc 1 B).lcm id) / 1189) ∧
      (∀ Y ≥ B, 1189 * (((Finset.Icc 1 Y).lcm id) / 1189) = (Finset.Icc 1 Y).lcm id ∧
        0 < ((Finset.Icc 1 Y).lcm id) / 1189) ∧
      (∀ q : ℕ, B < q →
        let L_prev := ((Finset.Icc 1 (q - 1)).lcm id) / 1189
        let L_curr := ((Finset.Icc 1 q).lcm id) / 1189
        let m_q := L_curr / L_prev
        m_q * L_prev = L_curr ∧ 1 ≤ m_q ∧ m_q ≤ q ∧
        ∀ m : ℕ, 1 ≤ m → m < m_q →
          ((L_prev : ℤ) ∣ ((m * L_prev : ℕ) : ℤ)) ∧ ¬ ((L_curr : ℤ) ∣ ((m * L_prev : ℕ) : ℤ))) := by
    have h_Y : ∀ Y ≥ B, 1189 * (((Finset.Icc 1 Y).lcm id) / 1189) = (Finset.Icc 1 Y).lcm id ∧
        0 < ((Finset.Icc 1 Y).lcm id) / 1189 := by
      intro Y hY
      set D := (Finset.Icc 1 Y).lcm id
      have h29 : 29 ∣ D := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have h41 : 41 ∣ D := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hcop : Nat.Coprime 29 41 := by decide
      have h1189 : 1189 ∣ D := by
        simpa using hcop.mul_dvd_of_dvd_of_dvd h29 h41
      have hD_pos : 0 < D := by
        refine Nat.pos_of_ne_zero ?_
        rw [ne_eq, Finset.lcm_eq_zero_iff]
        rintro ⟨x, hx, hx0⟩
        rw [Finset.mem_Icc] at hx
        simp only [id_eq] at hx0
        omega
      have hD_ge : 1189 ≤ D := Nat.le_of_dvd hD_pos h1189
      exact ⟨Nat.mul_div_cancel' h1189, by omega⟩
    refine ⟨(h_Y B (le_refl B)).2, h_Y, ?_⟩
    intro q hq
    dsimp only
    set D_prev := (Finset.Icc 1 (q - 1)).lcm id
    set D_curr := (Finset.Icc 1 q).lcm id
    set L_prev := D_prev / 1189
    set L_curr := D_curr / 1189
    set m_q := L_curr / L_prev
    have h_prev := h_Y (q - 1) (by omega)
    have h_curr := h_Y q (by omega)
    have hD_prev_eq : 1189 * L_prev = D_prev := h_prev.1
    have hL_prev_pos : 0 < L_prev := h_prev.2
    have hD_curr_eq : 1189 * L_curr = D_curr := h_curr.1
    have hL_curr_pos : 0 < L_curr := h_curr.2
    have hD_dvd : D_prev ∣ D_curr := by
      refine Finset.lcm_dvd ?_
      intro x hx
      exact Finset.dvd_lcm (Finset.Icc_subset_Icc_right (by omega) hx)
    have hL_dvd : L_prev ∣ L_curr := by
      rw [← hD_prev_eq, ← hD_curr_eq] at hD_dvd
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 1189)).mp hD_dvd
    have hm_eq : m_q * L_prev = L_curr := Nat.div_mul_cancel hL_dvd
    have hm_ge1 : 1 ≤ m_q := by
      refine Nat.pos_of_ne_zero ?_
      intro hm0
      rw [hm0, zero_mul] at hm_eq
      omega
    have hD_curr_dvd_mul : D_curr ∣ q * D_prev := by
      refine Finset.lcm_dvd ?_
      intro x hx
      rw [Finset.mem_Icc] at hx
      rcases eq_or_lt_of_le hx.2 with hxq | hlt
      · rw [hxq]; exact dvd_mul_right q D_prev
      · have hx_prev : x ∈ Finset.Icc 1 (q - 1) := Finset.mem_Icc.mpr ⟨hx.1, by omega⟩
        exact dvd_mul_of_dvd_right (Finset.dvd_lcm hx_prev) q
    have hD_prev_pos : 0 < D_prev := by omega
    have hD_curr_le : D_curr ≤ q * D_prev :=
      Nat.le_of_dvd (Nat.mul_pos (by omega) hD_prev_pos) hD_curr_dvd_mul
    have hm_le_q : m_q ≤ q := by
      have h1 : 1189 * (m_q * L_prev) ≤ 1189 * (q * L_prev) := by
        calc 1189 * (m_q * L_prev) = D_curr := by rw [hm_eq, hD_curr_eq]
          _ ≤ q * D_prev := hD_curr_le
          _ = q * (1189 * L_prev) := by rw [hD_prev_eq]
          _ = 1189 * (q * L_prev) := by ring
      have h2 : m_q * L_prev ≤ q * L_prev := Nat.le_of_mul_le_mul_left h1 (by decide)
      exact Nat.le_of_mul_le_mul_right h2 hL_prev_pos
    refine ⟨hm_eq, hm_ge1, hm_le_q, ?_⟩
    intro m hm1 hm_lt
    constructor
    · exact ⟨(m : ℤ), by push_cast; ring⟩
    · intro h_dvd_z
      have h_dvd_nat : L_curr ∣ m * L_prev := Int.ofNat_dvd.mp h_dvd_z
      have h_pos_mL : 0 < m * L_prev := Nat.mul_pos (by omega) hL_prev_pos
      have h_le : L_curr ≤ m * L_prev := Nat.le_of_dvd h_pos_mL h_dvd_nat
      have h_lt : m * L_prev < L_curr := by
        rw [← hm_eq]
        exact Nat.mul_lt_mul_of_pos_right hm_lt hL_prev_pos
      omega

  have h_sum_range_mul : ∀ (L₀ M : ℕ) (g : ℕ → ℝ),
      ∑ a ∈ Finset.range (M * L₀), g a =
        ∑ a₀ ∈ Finset.range L₀, ∑ m ∈ Finset.range M, g (a₀ + m * L₀) := by
    intro L₀ M g
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro a₀ _
      rw [Nat.add_comm]

  have h_periodic_Icc : ∀ (L : ℕ), 0 < L → ∀ (F : ℤ → ℝ),
      (∀ a : ℤ, 0 ≤ F a) →
      (∀ a : ℤ, F (a - (L : ℤ)) = F a) →
      ∑ a ∈ Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1), F a ≤
        2 * ∑ a ∈ Finset.range L, F (a : ℤ) := by
    intro L hL F h_nonneg h_per
    let S₁ : Finset ℤ := (Finset.range L).image (fun b : ℕ => (b : ℤ) - (L : ℤ))
    let S₂ : Finset ℤ := (Finset.range L).image (fun b : ℕ => (b : ℤ))
    have h_sub : Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1) ⊆ S₁ ∪ S₂ := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      by_cases ha0 : a < 0
      · left
        refine ⟨(a + (L : ℤ)).toNat, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
      · right
        refine ⟨a.toNat, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
    have h_disj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      rw [Finset.mem_image] at ha1 ha2
      rcases ha1 with ⟨b1, hb1, rfl⟩
      rcases ha2 with ⟨b2, hb2, h_eq⟩
      rw [Finset.mem_range] at hb1 hb2
      omega
    have h_le : ∑ a ∈ Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1), F a ≤
        ∑ a ∈ S₁ ∪ S₂, F a :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun a _ _ => h_nonneg a)
    have h_union : ∑ a ∈ S₁ ∪ S₂, F a = ∑ a ∈ S₁, F a + ∑ a ∈ S₂, F a :=
      Finset.sum_union h_disj
    have h_S₁ : ∑ a ∈ S₁, F a = ∑ b ∈ Finset.range L, F (b : ℤ) := by
      rw [Finset.sum_image (fun b1 _ b2 _ h => by omega)]
      refine Finset.sum_congr rfl ?_
      intro b _
      exact h_per (b : ℤ)
    have h_S₂ : ∑ a ∈ S₂, F a = ∑ b ∈ Finset.range L, F (b : ℤ) := by
      rw [Finset.sum_image (fun b1 _ b2 _ h => by omega)]
    linarith

  have h_single_mode : ∀ (M : ℕ), 0 < M → ∀ (A : ℝ) (N : ℤ),
      ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * (A + (m : ℝ) * (N : ℝ) / (M : ℝ))) ≤
        ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * ((m : ℝ) * (N : ℝ) / (M : ℝ))) := by
    intro M hM A N
    have hM_ne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    by_cases hdvd : (M : ℤ) ∣ N
    · rcases hdvd with ⟨c, hc⟩
      refine Finset.sum_le_sum ?_
      intro m _
      have h_arg : ∀ B : ℝ, 2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ)) =
          2 * Real.pi * B + (((m : ℤ) * c : ℤ) : ℝ) * (2 * Real.pi) := by
        intro B
        have hN_cast : (N : ℝ) = (M : ℝ) * (c : ℝ) := by exact_mod_cast hc
        rw [hN_cast]
        push_cast
        field_simp [hM_ne]
      rw [h_arg A, Real.cos_add_int_mul_two_pi]
      have h0 := h_arg 0
      simp only [zero_add] at h0
      rw [h0, Real.cos_add_int_mul_two_pi]
      simp only [mul_zero, Real.cos_zero]
      exact Real.cos_le_one _
    · have h_zero : ∀ B : ℝ, ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ))) = 0 := by
        intro B
        set x := Real.pi * (N : ℝ) / (M : ℝ)
        have hsin_ne : Real.sin x ≠ 0 := by
          intro hsin0
          rw [Real.sin_eq_zero_iff] at hsin0
          rcases hsin0 with ⟨k, hk⟩
          apply hdvd
          refine ⟨k, ?_⟩
          have h1 : (N : ℝ) = (M : ℝ) * (k : ℝ) := by
            dsimp [x] at hk
            have hk' : (k : ℝ) * Real.pi * (M : ℝ) = Real.pi * (N : ℝ) := by
              rw [hk, div_mul_cancel₀ _ hM_ne]
            have hk'' : Real.pi * (N : ℝ) = Real.pi * ((M : ℝ) * (k : ℝ)) := by linarith
            exact mul_left_cancel₀ hpi_ne hk''
          exact_mod_cast h1
        let g : ℕ → ℝ := fun m => Real.sin (2 * Real.pi * B + (2 * (m : ℝ) - 1) * x)
        have h_step : ∀ m : ℕ, 2 * Real.sin x * Real.cos (2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ))) =
            g (m + 1) - g m := by
          intro m
          dsimp [g, x]
          rw [Real.sin_sub_sin]
          have h_diff : (2 * Real.pi * B + (2 * ((m + 1 : ℕ) : ℝ) - 1) * (Real.pi * (N : ℝ) / (M : ℝ)) -
              (2 * Real.pi * B + (2 * (m : ℝ) - 1) * (Real.pi * (N : ℝ) / (M : ℝ)))) / 2 =
              Real.pi * (N : ℝ) / (M : ℝ) := by
            push_cast; ring
          have h_sum : (2 * Real.pi * B + (2 * ((m + 1 : ℕ) : ℝ) - 1) * (Real.pi * (N : ℝ) / (M : ℝ)) +
              (2 * Real.pi * B + (2 * (m : ℝ) - 1) * (Real.pi * (N : ℝ) / (M : ℝ)))) / 2 =
              2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ)) := by
            push_cast; ring
          rw [h_diff, h_sum]
        have h_mul_sum : 2 * Real.sin x * ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ))) =
            g M - g 0 := by
          rw [Finset.mul_sum]
          simp_rw [h_step]
          exact Finset.sum_range_sub g M
        have hgM : g M = g 0 := by
          dsimp [g, x]
          have h_eq : 2 * Real.pi * B + (2 * (M : ℝ) - 1) * (Real.pi * (N : ℝ) / (M : ℝ)) =
              (2 * Real.pi * B + (2 * (0 : ℝ) - 1) * (Real.pi * (N : ℝ) / (M : ℝ))) + (N : ℝ) * (2 * Real.pi) := by
            field_simp [hM_ne]; ring
          rw [Nat.cast_zero, h_eq, Real.sin_add_int_mul_two_pi]
        rw [hgM, sub_self] at h_mul_sum
        have h2sin : 2 * Real.sin x ≠ 0 := mul_ne_zero two_ne_zero hsin_ne
        exact (mul_eq_zero.mp h_mul_sum).resolve_left h2sin
      have hA := h_zero A
      have h0 := h_zero 0
      simp only [zero_add] at h0
      linarith

  have h_cos_pow : ∀ (M : ℕ), 0 < M → ∀ (Δ : Finset ℕ) (θ : ℕ → ℝ) (z : ℕ → ℤ) (n : ℕ) (A : ℝ) (N : ℤ),
      ∑ m ∈ Finset.range M,
        Real.cos (2 * Real.pi * (A + (m : ℝ) * (N : ℝ) / (M : ℝ))) *
          (∑ k ∈ Δ, (Real.cos (Real.pi * (θ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) ^ n ≤
      ∑ m ∈ Finset.range M,
        Real.cos (2 * Real.pi * ((m : ℝ) * (N : ℝ) / (M : ℝ))) *
          (∑ k ∈ Δ, (Real.cos (Real.pi * ((m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) ^ n := by
    intro M hM Δ θ z
    have h_trig : ∀ u v : ℝ, Real.cos u * (Real.cos v) ^ 2 =
        (1 / 2 : ℝ) * Real.cos u + (1 / 4 : ℝ) * Real.cos (u + (v + v)) + (1 / 4 : ℝ) * Real.cos (u - (v + v)) := by
      intro u v
      rw [Real.cos_add, Real.cos_sub, Real.cos_add]
      have h := Real.sin_sq_add_cos_sq v
      linear_combination (1 / 2 : ℝ) * Real.cos u * h
    let C : ℕ → ℝ := fun m => ∑ k ∈ Δ, (Real.cos (Real.pi * (θ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2
    let C₀ : ℕ → ℝ := fun m => ∑ k ∈ Δ, (Real.cos (Real.pi * ((m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2
    intro n
    induction n with
    | zero =>
      intro A N
      simp only [pow_zero, mul_one]
      exact h_single_mode M hM A N
    | succ n ih =>
      intro A N
      have h_expand : ∀ (B : ℝ) (ϕ : ℕ → ℝ) (D : ℕ → ℝ),
          (∀ m, D m = ∑ k ∈ Δ, (Real.cos (Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) →
          ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ))) * (D m) ^ (n + 1) =
          ∑ k ∈ Δ, (
            (1 / 2 : ℝ) * ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ))) * (D m) ^ n +
            (1 / 4 : ℝ) * ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * ((B + ϕ k) + (m : ℝ) * ((N + z k : ℤ) : ℝ) / (M : ℝ))) * (D m) ^ n +
            (1 / 4 : ℝ) * ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * ((B - ϕ k) + (m : ℝ) * ((N - z k : ℤ) : ℝ) / (M : ℝ))) * (D m) ^ n) := by
        intro B ϕ D hD
        have h_lhs : ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ))) * (D m) ^ (n + 1) =
            ∑ k ∈ Δ, ∑ m ∈ Finset.range M,
              (Real.cos (2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ))) *
                (Real.cos (Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) * (D m) ^ n := by
          rw [← Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro m _
          rw [pow_succ', hD m, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
        rw [h_lhs]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro m _
        rw [h_trig]
        have h_p : 2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ)) +
            (Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)) + Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ))) =
            2 * Real.pi * ((B + ϕ k) + (m : ℝ) * ((N + z k : ℤ) : ℝ) / (M : ℝ)) := by
          push_cast; ring
        have h_m : 2 * Real.pi * (B + (m : ℝ) * (N : ℝ) / (M : ℝ)) -
            (Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)) + Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ))) =
            2 * Real.pi * ((B - ϕ k) + (m : ℝ) * ((N - z k : ℤ) : ℝ) / (M : ℝ)) := by
          push_cast; ring
        rw [h_p, h_m]
        ring
      have h1 := h_expand A θ C (fun _ => rfl)
      have h2 := h_expand 0 (fun _ => 0) C₀ (fun m => by simp [C₀])
      simp only [zero_add, zero_sub, neg_zero] at h2
      change ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * (A + (m : ℝ) * (N : ℝ) / (M : ℝ))) * (C m) ^ (n + 1) ≤
        ∑ m ∈ Finset.range M, Real.cos (2 * Real.pi * ((m : ℝ) * (N : ℝ) / (M : ℝ))) * (C₀ m) ^ (n + 1)
      rw [h1, h2]
      refine Finset.sum_le_sum ?_
      intro k _
      have ih1 := ih A N
      have ih2 := ih (A + θ k) (N + z k)
      have ih3 := ih (A - θ k) (N - z k)
      linarith

  have h_fiber_contraction : ∀ (M : ℕ), 0 < M → ∀ (Δ : Finset ℕ) (θ : ℕ → ℝ) (z : ℕ → ℤ),
      ∑ m ∈ Finset.range M,
        Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * (θ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) ≤
      ∑ m ∈ Finset.range M,
        Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * ((m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) := by
    intro M hM Δ θ z
    let C : ℕ → ℝ := fun m => ∑ k ∈ Δ, (Real.cos (Real.pi * (θ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2
    let C₀ : ℕ → ℝ := fun m => ∑ k ∈ Δ, (Real.cos (Real.pi * ((m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2
    have h_pow_le : ∀ n : ℕ, ∑ m ∈ Finset.range M, (C m) ^ n ≤ ∑ m ∈ Finset.range M, (C₀ m) ^ n := by
      intro n
      have h := h_cos_pow M hM Δ θ z n 0 0
      simpa [C, C₀] using h
    have h_exp_C : ∑ m ∈ Finset.range M, Real.exp ((1 / 3 : ℝ) * C m) ≤
        ∑ m ∈ Finset.range M, Real.exp ((1 / 3 : ℝ) * C₀ m) := by
      have h_tsum_eq : ∀ f : ℕ → ℝ,
          ∑ m ∈ Finset.range M, Real.exp (f m) =
            ∑' n : ℕ, ∑ m ∈ Finset.range M, (f m) ^ n / (n.factorial : ℝ) := by
        intro f
        have h1 : ∀ m : ℕ, Real.exp (f m) = ∑' n : ℕ, (f m) ^ n / (n.factorial : ℝ) := by
          intro m
          rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
        simp_rw [h1]
        exact (Summable.tsum_finsetSum (fun m _ => Real.summable_pow_div_factorial (f m))).symm
      rw [h_tsum_eq (fun m => (1 / 3 : ℝ) * C m), h_tsum_eq (fun m => (1 / 3 : ℝ) * C₀ m)]
      refine Summable.tsum_le_tsum ?_
        (summable_sum (fun m _ => Real.summable_pow_div_factorial ((1 / 3 : ℝ) * C m)))
        (summable_sum (fun m _ => Real.summable_pow_div_factorial ((1 / 3 : ℝ) * C₀ m)))
      intro n
      have h_factor : ∀ D : ℕ → ℝ,
          ∑ m ∈ Finset.range M, ((1 / 3 : ℝ) * D m) ^ n / (n.factorial : ℝ) =
            ((1 / 3 : ℝ) ^ n / (n.factorial : ℝ)) * ∑ m ∈ Finset.range M, (D m) ^ n := by
        intro D
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _
        rw [mul_pow]
        ring
      rw [h_factor C, h_factor C₀]
      refine mul_le_mul_of_nonneg_left (h_pow_le n) ?_
      positivity
    have h_sin_cos : ∀ (ϕ : ℕ → ℝ) (D : ℕ → ℝ),
        (∀ m, D m = ∑ k ∈ Δ, (Real.cos (Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) →
        ∀ m : ℕ, Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) =
          Real.exp (- (1 / 3 : ℝ) * (Δ.card : ℝ)) * Real.exp ((1 / 3 : ℝ) * D m) := by
      intro ϕ D hD m
      rw [← Real.exp_add]
      congr 1
      have h_sum_sin : ∑ k ∈ Δ, (Real.sin (Real.pi * (ϕ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2 =
          (Δ.card : ℝ) - D m := by
        rw [hD m, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
        have h_ones : ∑ x ∈ Δ, ((Real.sin (Real.pi * (ϕ x + (m : ℝ) * (z x : ℝ) / (M : ℝ)))) ^ 2 +
            (Real.cos (Real.pi * (ϕ x + (m : ℝ) * (z x : ℝ) / (M : ℝ)))) ^ 2) = ∑ _x ∈ Δ, (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          exact Real.sin_sq_add_cos_sq _
        rw [h_ones, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h_sum_sin]
      ring
    have hL : ∑ m ∈ Finset.range M,
        Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * (θ k + (m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) =
        Real.exp (- (1 / 3 : ℝ) * (Δ.card : ℝ)) * ∑ m ∈ Finset.range M, Real.exp ((1 / 3 : ℝ) * C m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      exact h_sin_cos θ C (fun _ => rfl) m
    have hR : ∑ m ∈ Finset.range M,
        Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * ((m : ℝ) * (z k : ℝ) / (M : ℝ)))) ^ 2) =
        Real.exp (- (1 / 3 : ℝ) * (Δ.card : ℝ)) * ∑ m ∈ Finset.range M, Real.exp ((1 / 3 : ℝ) * C₀ m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      simpa using h_sin_cos (fun _ => 0) C₀ (fun m => by simp [C₀]) m
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left h_exp_C (le_of_lt (Real.exp_pos _))

  set D : ℕ → ℕ := fun n => (Finset.Icc 1 n).lcm id
  set L : ℕ → ℕ := fun n => D n / 1189
  set r : ℕ → ℝ := fun k => 1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)
  set F : ℕ → ℤ → ℝ := fun Y a =>
    Real.exp (- (1 / 3 : ℝ) * ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * r i.1)) ^ 2)
  set S : ℕ → ℝ := fun Y => ∑ a ∈ Finset.range (L Y), F Y (a : ℤ)
  obtain ⟨hLB_pos, hL_Y, hL_step⟩ := h_lcm_props
  let z_num : ℕ → ℕ → ℤ := fun Y k => ((((D Y : ℕ) : ℚ) * w_Icc (I_seq k).1 (I_seq k).2).num)
  have h_Lr_eq : ∀ Y ≥ B, ∀ k < l_seq Y, (L Y : ℝ) * r k = (z_num Y k : ℝ) := by
    intro Y hY k hk
    have hden := h_den Y hY ⟨k, hk⟩
    have hrat : ((z_num Y k : ℤ) : ℚ) = ((D Y : ℕ) : ℚ) * w_Icc (I_seq k).1 (I_seq k).2 := by
      dsimp [z_num]
      have h_div := Rat.num_div_den (((D Y : ℕ) : ℚ) * w_Icc (I_seq k).1 (I_seq k).2)
      rw [hden, Nat.cast_one, div_one] at h_div
      exact h_div
    have hreal : (z_num Y k : ℝ) = (D Y : ℝ) * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ) := by
      exact_mod_cast hrat
    have hDY : (D Y : ℝ) = 1189 * (L Y : ℝ) := by
      exact_mod_cast (hL_Y Y hY).1.symm
    rw [hreal, hDY]
    dsimp [r]
    ring
  have hF_per_shift : ∀ Y ≥ B, ∀ (a c : ℤ), F Y (a + c * (L Y : ℤ)) = F Y a := by
    intro Y hY a c
    dsimp [F]
    congr 2
    refine Finset.sum_congr rfl ?_
    intro i _
    have hLr := h_Lr_eq Y hY i.1 i.2
    have h_arg : Real.pi * ((a + c * (L Y : ℤ) : ℤ) : ℝ) * r i.1 =
        Real.pi * (a : ℝ) * r i.1 + ((c * z_num Y i.1 : ℤ) : ℝ) * Real.pi := by
      calc Real.pi * ((a + c * (L Y : ℤ) : ℤ) : ℝ) * r i.1
          = Real.pi * (a : ℝ) * r i.1 + Real.pi * (c : ℝ) * ((L Y : ℝ) * r i.1) := by
            push_cast; ring
        _ = Real.pi * (a : ℝ) * r i.1 + Real.pi * (c : ℝ) * (z_num Y i.1 : ℝ) := by rw [hLr]
        _ = Real.pi * (a : ℝ) * r i.1 + ((c * z_num Y i.1 : ℤ) : ℝ) * Real.pi := by
            push_cast; ring
    rw [h_arg, Real.sin_add_int_mul_pi]
    rw [← sq_abs ((-1 : ℝ) ^ (c * z_num Y i.1) * _), abs_mul, abs_zpow, abs_neg, abs_one,
      one_zpow, one_mul, sq_abs]
  have h_step_bound : ∀ q : ℕ, B < q → S q ≤ Real.exp (((q : ℝ) ^ 3)⁻¹) * S (q - 1) := by
    intro q hq
    have hq1_B : B ≤ q - 1 := by omega
    have hq_B : B ≤ q := by omega
    obtain ⟨hm_eq, hm_ge1, hm_le_q, hm_dvd⟩ := hL_step q hq
    set m_q := L q / L (q - 1)
    have hm_eq' : m_q * L (q - 1) = L q := hm_eq
    have h_S_eq : S q = ∑ a₀ ∈ Finset.range (L (q - 1)), ∑ m ∈ Finset.range m_q,
        F q ((a₀ + m * L (q - 1) : ℕ) : ℤ) := by
      dsimp [S]
      rw [← hm_eq']
      exact h_sum_range_mul (L (q - 1)) m_q (fun a => F q (a : ℤ))
    set Δ := Finset.range (l_seq q) \ Finset.range (l_seq (q - 1))
    have h_F_split : ∀ (a₀ m : ℕ),
        F q ((a₀ + m * L (q - 1) : ℕ) : ℤ) =
          F (q - 1) (a₀ : ℤ) *
            Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ,
              (Real.sin (Real.pi * ((a₀ : ℝ) * r k + (m : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)))) ^ 2) := by
      intro a₀ m
      set b : ℤ := (a₀ : ℤ) + (m : ℤ) * (L (q - 1) : ℤ)
      have hb_eq : ((a₀ + m * L (q - 1) : ℕ) : ℤ) = b := by
        dsimp [b]
      rw [hb_eq]
      have h_per0 : F (q - 1) b = F (q - 1) (a₀ : ℤ) :=
        hF_per_shift (q - 1) hq1_B (a₀ : ℤ) (m : ℤ)
      rw [← h_per0]
      dsimp [F]
      rw [← Real.exp_add]
      congr 1
      have h_sum_q : ∑ i : Fin (l_seq q), (Real.sin (Real.pi * (b : ℝ) * r i.1)) ^ 2 =
          ∑ k ∈ Finset.range (l_seq q), (Real.sin (Real.pi * (b : ℝ) * r k)) ^ 2 :=
        Fin.sum_univ_eq_sum_range (fun k => (Real.sin (Real.pi * (b : ℝ) * r k)) ^ 2) (l_seq q)
      have h_sum_q1 : ∑ i : Fin (l_seq (q - 1)), (Real.sin (Real.pi * (b : ℝ) * r i.1)) ^ 2 =
          ∑ k ∈ Finset.range (l_seq (q - 1)), (Real.sin (Real.pi * (b : ℝ) * r k)) ^ 2 :=
        Fin.sum_univ_eq_sum_range (fun k => (Real.sin (Real.pi * (b : ℝ) * r k)) ^ 2) (l_seq (q - 1))
      rw [h_sum_q, h_sum_q1]
      have h_sub : Finset.range (l_seq (q - 1)) ⊆ Finset.range (l_seq q) :=
        Finset.range_subset_range.mpr (h_mono.2 (q - 1) q (by omega))
      rw [← Finset.sum_sdiff h_sub]
      have h_delta_eq : ∑ k ∈ Δ, (Real.sin (Real.pi * (b : ℝ) * r k)) ^ 2 =
          ∑ k ∈ Δ, (Real.sin (Real.pi * ((a₀ : ℝ) * r k + (m : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)))) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hk_lt : k < l_seq q := Finset.mem_range.mp (Finset.sdiff_subset hk)
        have hLr := h_Lr_eq q hq_B k hk_lt
        have hm_ne : (m_q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have h_L_mul : (m_q : ℝ) * (L (q - 1) : ℝ) = (L q : ℝ) := by exact_mod_cast hm_eq'
        have h_rk : (L (q - 1) : ℝ) * r k = (z_num q k : ℝ) / (m_q : ℝ) := by
          rw [eq_div_iff hm_ne]
          calc (L (q - 1) : ℝ) * r k * (m_q : ℝ) = ((m_q : ℝ) * (L (q - 1) : ℝ)) * r k := by ring
            _ = (L q : ℝ) * r k := by rw [h_L_mul]
            _ = (z_num q k : ℝ) := hLr
        have h_in : Real.pi * (b : ℝ) * r k =
            Real.pi * ((a₀ : ℝ) * r k + (m : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)) := by
          calc Real.pi * (b : ℝ) * r k
              = Real.pi * ((a₀ : ℝ) * r k + (m : ℝ) * ((L (q - 1) : ℝ) * r k)) := by
                dsimp [b]; push_cast; ring
            _ = Real.pi * ((a₀ : ℝ) * r k + (m : ℝ) * ((z_num q k : ℝ) / (m_q : ℝ))) := by rw [h_rk]
            _ = Real.pi * ((a₀ : ℝ) * r k + (m : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)) := by ring
        rw [h_in]
      rw [h_delta_eq]
      ring
    have h_zero_term : ∑ m ∈ Finset.range m_q,
        Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * ((m : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)))) ^ 2) ≤
        Real.exp (((q : ℝ) ^ 3)⁻¹) := by
      let g : ℕ → ℝ := fun m =>
        Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * ((m : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)))) ^ 2)
      have hm_succ : m_q = (m_q - 1) + 1 := by omega
      change ∑ m ∈ Finset.range m_q, g m ≤ Real.exp (((q : ℝ) ^ 3)⁻¹)
      rw [hm_succ, Finset.sum_range_succ']
      have hg0 : g 0 = 1 := by
        dsimp [g]; simp
      have hg_pos : ∀ i ∈ Finset.range (m_q - 1), g (i + 1) ≤ ((q : ℝ) ^ 4)⁻¹ := by
        intro i hi
        have hi_lt : i + 1 < m_q := by
          rw [Finset.mem_range] at hi; omega
        have hi_dvd := hm_dvd (i + 1) (by omega) hi_lt
        have h_energy := h_step_energy q hq (((i + 1) * L (q - 1) : ℕ) : ℤ) hi_dvd.1 hi_dvd.2
        have h_energy' : 12 * Real.log (q : ℝ) ≤
            ∑ k ∈ Δ, (Real.sin (Real.pi * ((((i + 1) * L (q - 1) : ℕ) : ℤ) : ℝ) * r k)) ^ 2 := h_energy
        have h_sum_eq : ∑ k ∈ Δ, (Real.sin (Real.pi * (((i + 1 : ℕ) : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)))) ^ 2 =
            ∑ k ∈ Δ, (Real.sin (Real.pi * ((((i + 1) * L (q - 1) : ℕ) : ℤ) : ℝ) * r k)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_lt : k < l_seq q := Finset.mem_range.mp (Finset.sdiff_subset hk)
          have hLr := h_Lr_eq q hq_B k hk_lt
          have hm_ne : (m_q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have h_L_mul : (m_q : ℝ) * (L (q - 1) : ℝ) = (L q : ℝ) := by exact_mod_cast hm_eq'
          have h_rk : (L (q - 1) : ℝ) * r k = (z_num q k : ℝ) / (m_q : ℝ) := by
            rw [eq_div_iff hm_ne]
            calc (L (q - 1) : ℝ) * r k * (m_q : ℝ) = ((m_q : ℝ) * (L (q - 1) : ℝ)) * r k := by ring
              _ = (L q : ℝ) * r k := by rw [h_L_mul]
              _ = (z_num q k : ℝ) := hLr
          have h_in : Real.pi * (((i + 1 : ℕ) : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)) =
              Real.pi * ((((i + 1) * L (q - 1) : ℕ) : ℤ) : ℝ) * r k := by
            calc Real.pi * (((i + 1 : ℕ) : ℝ) * (z_num q k : ℝ) / (m_q : ℝ))
                = Real.pi * (((i + 1 : ℕ) : ℝ) * ((z_num q k : ℝ) / (m_q : ℝ))) := by ring
              _ = Real.pi * (((i + 1 : ℕ) : ℝ) * ((L (q - 1) : ℝ) * r k)) := by rw [← h_rk]
              _ = Real.pi * ((((i + 1) * L (q - 1) : ℕ) : ℤ) : ℝ) * r k := by push_cast; ring
          rw [h_in]
        dsimp [g]
        rw [h_sum_eq]
        have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
        have h_log4 : Real.log ((q : ℝ) ^ 4) = 4 * Real.log (q : ℝ) := by
          rw [Real.log_pow]; norm_num
        have h_exp_le : - (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * ((((i + 1) * L (q - 1) : ℕ) : ℤ) : ℝ) * r k)) ^ 2 ≤
            - Real.log ((q : ℝ) ^ 4) := by
          rw [h_log4]
          linarith [h_energy']
        calc Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ, (Real.sin (Real.pi * ((((i + 1) * L (q - 1) : ℕ) : ℤ) : ℝ) * r k)) ^ 2)
            ≤ Real.exp (- Real.log ((q : ℝ) ^ 4)) := Real.exp_le_exp.mpr h_exp_le
          _ = (Real.exp (Real.log ((q : ℝ) ^ 4)))⁻¹ := Real.exp_neg _
          _ = ((q : ℝ) ^ 4)⁻¹ := by rw [Real.exp_log (by positivity)]
      have h_sum_le := Finset.sum_le_card_nsmul (Finset.range (m_q - 1)) (fun i => g (i + 1)) (((q : ℝ) ^ 4)⁻¹) hg_pos
      rw [Finset.card_range, nsmul_eq_mul] at h_sum_le
      have hm1_le_q : ((m_q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : m_q - 1 ≤ q)
      have h_mul_le : ((m_q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ 4)⁻¹ ≤ ((q : ℝ) ^ 3)⁻¹ := by
        have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        calc ((m_q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ 4)⁻¹
            ≤ (q : ℝ) * ((q : ℝ) ^ 4)⁻¹ := mul_le_mul_of_nonneg_right hm1_le_q (by positivity)
          _ = ((q : ℝ) ^ 3)⁻¹ := by field_simp [hq_ne]
      have h_exp_1 := Real.add_one_le_exp (((q : ℝ) ^ 3)⁻¹)
      linarith
    rw [h_S_eq, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro a₀ _
    have h_inner : ∑ m ∈ Finset.range m_q, F q ((a₀ + m * L (q - 1) : ℕ) : ℤ) =
        F (q - 1) (a₀ : ℤ) * ∑ m ∈ Finset.range m_q,
          Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Δ,
            (Real.sin (Real.pi * ((a₀ : ℝ) * r k + (m : ℝ) * (z_num q k : ℝ) / (m_q : ℝ)))) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      exact h_F_split a₀ m
    rw [h_inner, mul_comm (Real.exp (((q : ℝ) ^ 3)⁻¹)) (F (q - 1) (a₀ : ℤ))]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
    exact le_trans (h_fiber_contraction m_q (by omega) Δ (fun k => (a₀ : ℝ) * r k) (fun k => z_num q k)) h_zero_term
  have h_ind : ∀ d : ℕ, S (B + d) ≤ (L B : ℝ) * Real.exp ((1 : ℝ) / (B : ℝ) - (1 : ℝ) / ((B + d : ℕ) : ℝ)) := by
    intro d
    induction d with
    | zero =>
      simp only [Nat.add_zero, sub_self, Real.exp_zero, mul_one]
      have h_le_one : ∀ a ∈ Finset.range (L B), F B (a : ℤ) ≤ 1 := by
        intro a _
        dsimp [F]
        rw [Real.exp_le_one_iff]
        have h_sum_nonneg : 0 ≤ ∑ i : Fin (l_seq B), (Real.sin (Real.pi * ((a : ℤ) : ℝ) * r i.1)) ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        linarith
      have h_sum := Finset.sum_le_card_nsmul (Finset.range (L B)) (fun a => F B (a : ℤ)) 1 h_le_one
      simpa [S] using h_sum
    | succ d ih =>
      set q := B + d + 1
      have hq_gt : B < q := by omega
      have hq_sub : q - 1 = B + d := by omega
      have h_Bd1 : B + (d + 1) = q := by omega
      rw [h_Bd1]
      have h_step := h_step_bound q hq_gt
      rw [hq_sub] at h_step
      have h_mul : S q ≤ (L B : ℝ) * (Real.exp (((q : ℝ) ^ 3)⁻¹) * Real.exp ((1 : ℝ) / (B : ℝ) - (1 : ℝ) / ((B + d : ℕ) : ℝ))) := by
        calc S q ≤ Real.exp (((q : ℝ) ^ 3)⁻¹) * S (B + d) := h_step
          _ ≤ Real.exp (((q : ℝ) ^ 3)⁻¹) * ((L B : ℝ) * Real.exp ((1 : ℝ) / (B : ℝ) - (1 : ℝ) / ((B + d : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
          _ = (L B : ℝ) * (Real.exp (((q : ℝ) ^ 3)⁻¹) * Real.exp ((1 : ℝ) / (B : ℝ) - (1 : ℝ) / ((B + d : ℕ) : ℝ))) := by ring
      rw [← Real.exp_add] at h_mul
      refine le_trans h_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
      have hq1_pos : (0 : ℝ) < ((B + d : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
      have hq_eq : (q : ℝ) = ((B + d : ℕ) : ℝ) + 1 := by
        dsimp [q]; push_cast; ring
      have h_inv_le : ((q : ℝ) ^ 3)⁻¹ ≤ (1 : ℝ) / ((B + d : ℕ) : ℝ) - (1 : ℝ) / (q : ℝ) := by
        have h_diff_eq : (1 : ℝ) / ((B + d : ℕ) : ℝ) - (1 : ℝ) / (q : ℝ) = (((B + d : ℕ) : ℝ) * (q : ℝ))⁻¹ := by
          rw [hq_eq]
          field_simp [ne_of_gt hq1_pos, ne_of_gt hq_pos]
          ring
        rw [h_diff_eq]
        refine inv_anti₀ (mul_pos hq1_pos hq_pos) ?_
        have h_nat_le : (B + d) * q ≤ q ^ 3 := by
          calc (B + d) * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
            _ ≤ q * q * q := Nat.le_mul_of_pos_right (q * q) (by omega)
            _ = q ^ 3 := by ring
        exact_mod_cast h_nat_le
      linarith [h_inv_le]

  refine ⟨(6 * L B : ℚ), ?_, ?_⟩
  · have : (0 : ℚ) < (L B : ℚ) := Nat.cast_pos.mpr hLB_pos
    positivity
  · intro Y hY
    have h_per_Y : ∀ a : ℤ, F Y (a - (L Y : ℤ)) = F Y a := by
      intro a
      have h_eq : a - (L Y : ℤ) = a + (-1 : ℤ) * (L Y : ℤ) := by ring
      rw [h_eq]
      exact hF_per_shift Y hY a (-1)
    have h_Icc_le : ∑ a ∈ Finset.Icc (-(L Y : ℤ) / 2) (((L Y : ℤ) + 1) / 2 - 1), F Y a ≤
        2 * S Y := by
      exact h_periodic_Icc (L Y) (hL_Y Y hY).2 (F Y) (fun a => le_of_lt (Real.exp_pos _)) h_per_Y
    have h_SY_le : S Y ≤ 3 * (L B : ℝ) := by
      have h_Y_eq : B + (Y - B) = Y := Nat.add_sub_of_le hY
      have h_bound := h_ind (Y - B)
      rw [h_Y_eq] at h_bound
      have h_exp_le_3 : Real.exp ((1 : ℝ) / (B : ℝ) - (1 : ℝ) / (Y : ℝ)) ≤ 3 := by
        have hB_ge1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
        have hB_inv_le1 : (1 : ℝ) / (B : ℝ) ≤ 1 := div_le_one_of_le₀ hB_ge1 (by positivity)
        have hY_inv_nonneg : 0 ≤ (1 : ℝ) / (Y : ℝ) := by positivity
        have h_exp1 : Real.exp ((1 : ℝ) / (B : ℝ) - (1 : ℝ) / (Y : ℝ)) ≤ Real.exp 1 :=
          Real.exp_le_exp.mpr (by linarith)
        have h_e_lt := Real.exp_one_lt_d9
        linarith
      calc S Y ≤ (L B : ℝ) * Real.exp ((1 : ℝ) / (B : ℝ) - (1 : ℝ) / (Y : ℝ)) := h_bound
        _ ≤ (L B : ℝ) * 3 := mul_le_mul_of_nonneg_left h_exp_le_3 (by positivity)
        _ = 3 * (L B : ℝ) := by ring
    change ∑ a ∈ Finset.Icc (-(L Y : ℤ) / 2) (((L Y : ℤ) + 1) / 2 - 1), F Y a ≤ ((6 * (L B : ℚ) : ℚ) : ℝ)
    push_cast
    linarith

theorem nested_reserve_with_sine_energy_existence : ∃ (B : ℕ) (C_m : ℚ) (l_seq : ℕ → ℕ) (I_seq : ℕ → ℕ × ℕ),
      1189 ≤ B ∧ 0 < C_m ∧
      (∀ k : ℕ, 495 ≤ (I_seq k).1 ∧ (I_seq k).1 < (I_seq k).2 ∧ (I_seq k).2 ≤ (I_seq k).1 + 2) ∧
      (∀ k m : ℕ, k ≠ m → (I_seq k).2 + 1 < (I_seq m).1 ∨ (I_seq m).2 + 1 < (I_seq k).1) ∧
      (1 ≤ l_seq B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_seq Y₁ ≤ l_seq Y₂) ∧
      (∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_seq k).1 (I_seq k).2 ≤ 1 / 118900) ∧
      (∀ Y ≥ B, l_seq Y ≤ 2 ^ 57 * Y * (Nat.log 2 Y + 1) ^ 3 ∧
        ∀ i : Fin (l_seq Y), ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (I_seq i.1).1 (I_seq i.1).2).den = 1) ∧
      (∀ Y ≥ B,
        ∑ a ∈ Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2) ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1),
          Real.exp (- (1 / 3 : ℝ) * ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2) ≤ (C_m : ℝ)) ∧
      (∀ M : ℝ, 0 < M → ∃ (C_M Y_M : ℕ), B ≤ Y_M ∧ 1 ≤ C_M ∧
        ∀ Y ≥ Y_M, ∀ a ∈ (Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2) ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1)) \
            (Finset.Icc (-(C_M : ℤ)) (C_M : ℤ)),
          M ≤ ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2) :=
by
  classical
  obtain ⟨B, l_dig, I_dig, hB, h_dig_bounds, h_dig_sep, h_dig_mono, h_dig_mass, h_dig_scale, h_dig_energy⟩ :=
    coherent_digit_reserve_existence
  obtain ⟨l_seq, I_seq, h_bounds, h_sep, h_mono, h_mass, h_scale_lcm, h_step_energy, h_rigidity⟩ :=
    lacunary_rigidity_and_combined_reserve_merge B l_dig I_dig hB h_dig_bounds h_dig_sep h_dig_mono h_dig_mass h_dig_scale h_dig_energy
  obtain ⟨C_m, hCm, h_kern⟩ :=
    complete_period_gaussian_sine_kernel_bound B l_seq I_seq hB h_mono (fun Y hY => (h_scale_lcm Y hY).2) h_step_energy
  refine ⟨B, C_m, l_seq, I_seq, hB, hCm, h_bounds, h_sep, h_mono, h_mass, h_scale_lcm, h_kern, ?_⟩
  
  intro M hM
  by_contra! h_contra
  have h_ex : ∀ j : ℕ, ∃ Y : ℕ, B + j ≤ Y ∧ ∃ a : ℤ,
      a ∈ (Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2)
        ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1)) \
        (Finset.Icc (-((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ)) ∧
      ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 < M := by
    intro j
    exact h_contra (j + 1) (B + j) (by omega) (by omega)
  let Y_seq : ℕ → ℕ := fun j => Classical.choose (h_ex j)
  have hY_spec : ∀ j : ℕ, B + j ≤ Y_seq j ∧ ∃ a : ℤ,
      a ∈ (Finset.Icc (-((((Finset.Icc 1 (Y_seq j)).lcm id) / 1189 : ℕ) : ℤ) / 2)
        ((((((Finset.Icc 1 (Y_seq j)).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1)) \
        (Finset.Icc (-((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ)) ∧
      ∑ i : Fin (l_seq (Y_seq j)), (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 < M :=
    fun j => Classical.choose_spec (h_ex j)
  let a_seq : ℕ → ℤ := fun j => Classical.choose (hY_spec j).2
  have ha_spec : ∀ j : ℕ,
      a_seq j ∈ (Finset.Icc (-((((Finset.Icc 1 (Y_seq j)).lcm id) / 1189 : ℕ) : ℤ) / 2)
        ((((((Finset.Icc 1 (Y_seq j)).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1)) \
        (Finset.Icc (-((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ)) ∧
      ∑ i : Fin (l_seq (Y_seq j)), (Real.sin (Real.pi * (a_seq j : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 < M :=
    fun j => Classical.choose_spec (hY_spec j).2
  obtain ⟨a_star, ha_star_energy, ha_star_div⟩ :=
    h_rigidity M hM Y_seq a_seq (fun j => ⟨(hY_spec j).1, le_of_lt (ha_spec j).2⟩)
  let Q : ℕ := max B (max (Nat.ceil (Real.exp M) + 2) (2378 * (a_star.natAbs + 2)))
  have hB_le_Q : B ≤ Q := le_max_left _ _
  have hexp_le_Q : Nat.ceil (Real.exp M) + 2 ≤ Q := le_trans (le_max_left _ _) (le_max_right _ _)
  have habs_le_Q : 2378 * (a_star.natAbs + 2) ≤ Q := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨j, hj_ge_Q, hj_dvd⟩ := ha_star_div Q hB_le_Q
  set Y := Y_seq j
  set δ : ℤ := a_seq j - a_star
  have hQ_le_Y : Q ≤ Y := by
    have := (hY_spec j).1
    omega
  have hB_le_Y : B ≤ Y := le_trans hB_le_Q hQ_le_Y
  have h_sin_sub_sq : ∀ α β : ℝ, (Real.sin (α - β)) ^ 2 ≤ 2 * (Real.sin α) ^ 2 + 2 * (Real.sin β) ^ 2 := by
    intro α β
    rw [Real.sin_sub]
    have hc1 : (Real.cos β) ^ 2 ≤ 1 := Real.cos_sq_le_one β
    have hc2 : (Real.cos α) ^ 2 ≤ 1 := Real.cos_sq_le_one α
    have hs1 : 0 ≤ (Real.sin α) ^ 2 := sq_nonneg _
    have hs2 : 0 ≤ (Real.sin β) ^ 2 := sq_nonneg _
    have h_diff : (Real.sin α * Real.cos β - Real.cos α * Real.sin β) ^ 2 ≤
        2 * ((Real.sin α) ^ 2 * (Real.cos β) ^ 2) + 2 * ((Real.cos α) ^ 2 * (Real.sin β) ^ 2) := by
      have : 0 ≤ (Real.sin α * Real.cos β + Real.cos α * Real.sin β) ^ 2 := sq_nonneg _
      linarith
    nlinarith
  have h_delta_energy : ∑ i : Fin (l_seq Y),
      (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ 4 * M := by
    have h_term : ∀ i : Fin (l_seq Y),
        (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤
          2 * (Real.sin (Real.pi * (a_seq j : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 +
          2 * (Real.sin (Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 := by
      intro i
      have h_eq : Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) =
          Real.pi * (a_seq j : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) -
          Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)) := by
        push_cast [δ]
        ring
      rw [h_eq]
      exact h_sin_sub_sq _ _
    have h_sum_le := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h_term i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h_sum_le
    have h1 : ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a_seq j : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ M :=
      le_of_lt (ha_spec j).2
    have h2 : ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a_star : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 ≤ M :=
      ha_star_energy Y hB_le_Y
    linarith
  have h_log_Q : M < Real.log (Q : ℝ) := by
    have h1 : Real.exp M ≤ (Nat.ceil (Real.exp M) : ℝ) := Nat.le_ceil (Real.exp M)
    have h2 : (Nat.ceil (Real.exp M) : ℝ) < (Q : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp M) < Q)
    have h3 : Real.exp M < (Q : ℝ) := lt_of_le_of_lt h1 h2
    have hQ_pos : (0 : ℝ) < (Q : ℝ) := lt_trans (Real.exp_pos M) h3
    rw [← Real.log_exp M]
    exact Real.log_lt_log (Real.exp_pos M) h3
  have h_ind_dvd : ∀ d : ℕ, Q + d ≤ Y →
      ((((Finset.Icc 1 (Q + d)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa using hj_dvd
    | succ d ih =>
      intro hdY
      have hd_prev : ((((Finset.Icc 1 (Q + d)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ := ih (by omega)
      by_contra h_not_dvd
      set q := Q + d + 1
      have hB_lt_q : B < q := by omega
      have hq_sub : q - 1 = Q + d := by omega
      have hd_prev' : ((((Finset.Icc 1 (q - 1)).lcm id) / 1189 : ℕ) : ℤ) ∣ δ := by
        rwa [hq_sub]
      have h_step := h_step_energy q hB_lt_q δ hd_prev' h_not_dvd
      have h_sub_range : (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))) ⊆ Finset.range (l_seq Y) := by
        refine Finset.Subset.trans Finset.sdiff_subset ?_
        exact Finset.range_subset_range.mpr (h_mono.2 q Y hdY)
      have h_slice_le : ∑ k ∈ (Finset.range (l_seq q)) \ (Finset.range (l_seq (q - 1))),
          (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)))) ^ 2 ≤
          ∑ i : Fin (l_seq Y),
            (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun k => (Real.sin (Real.pi * (δ : ℝ) * (1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)))) ^ 2) (l_seq Y)]
        refine Finset.sum_le_sum_of_subset_of_nonneg h_sub_range ?_
        intro k _ _
        exact sq_nonneg _
      have h_log_q : Real.log (Q : ℝ) ≤ Real.log (q : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast (by omega : 0 < Q)
        · exact_mod_cast (by omega : Q ≤ q)
      linarith
  have hY_dvd : ((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) ∣ δ := by
    have h := h_ind_dvd (Y - Q) (by omega)
    rwa [Nat.add_sub_of_le hQ_le_Y] at h
  set L_Y : ℕ := ((Finset.Icc 1 Y).lcm id) / 1189
  have hD_pos : 0 < (Finset.Icc 1 Y).lcm id := by
    refine Nat.pos_of_ne_zero ?_
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    intro ⟨x, hx, hx0⟩
    rw [Finset.mem_Icc] at hx
    simp only [id_eq] at hx0
    omega
  have hY_dvd_D : Y ∣ (Finset.Icc 1 Y).lcm id := by
    have hY_mem : Y ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨by omega, le_refl Y⟩
    exact Finset.dvd_lcm hY_mem
  have hY_le_D : Y ≤ (Finset.Icc 1 Y).lcm id := Nat.le_of_dvd hD_pos hY_dvd_D
  have hL_ge : 2 * (a_star.natAbs + 2) ≤ L_Y := by
    have hQ_le_D : 2378 * (a_star.natAbs + 2) ≤ (Finset.Icc 1 Y).lcm id :=
      le_trans habs_le_Q (le_trans hQ_le_Y hY_le_D)
    dsimp [L_Y]
    omega
  have ha_in_sdiff : a_seq j ∈ (Finset.Icc (-(L_Y : ℤ) / 2) (((L_Y : ℤ) + 1) / 2 - 1)) \
      (Finset.Icc (-((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ)) := (ha_spec j).1
  have ha_mem := (Finset.mem_sdiff.mp ha_in_sdiff).1
  rw [Finset.mem_Icc] at ha_mem
  have ha_not_mem := (Finset.mem_sdiff.mp ha_in_sdiff).2
  rw [Finset.mem_Icc] at ha_not_mem
  have h_abs_astar : |(a_star : ℤ)| = (a_star.natAbs : ℤ) := Int.abs_eq_natAbs a_star
  have h_astar_bounds : -((a_star.natAbs : ℕ) : ℤ) ≤ a_star ∧ a_star ≤ ((a_star.natAbs : ℕ) : ℤ) :=
    abs_le.mp (le_of_eq h_abs_astar)
  have h_delta_abs_lt : |δ| < (L_Y : ℤ) := by
    rw [abs_lt]
    dsimp [δ]
    omega
  have h_delta_zero : δ = 0 := Int.eq_zero_of_abs_lt_dvd hY_dvd h_delta_abs_lt
  have ha_eq : a_seq j = a_star := sub_eq_zero.mp h_delta_zero
  apply ha_not_mem
  rw [ha_eq]
  omega

theorem fejer_kernel_nonneg_and_exterior_bound (m : ℕ) (hm : 1 ≤ m) (u : ℝ) :
    (0 ≤ ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (1 - |(a : ℝ)| / (m : ℝ)) * Real.cos (2 * Real.pi * (a : ℝ) * u)) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → δ ≤ -u → -u ≤ 1 - δ →
      ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (1 - |(a : ℝ)| / (m : ℝ)) * Real.cos (2 * Real.pi * (a : ℝ) * u) ≤
        1 / ((m : ℝ) * (Real.sin (Real.pi * δ)) ^ 2)) :=
by
  let D : ℕ → ℝ := fun k =>
    ∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * u)
  let W : ℕ → ℝ := fun k =>
    ∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ((k : ℝ) - |(a : ℝ)|) * Real.cos (2 * Real.pi * (a : ℝ) * u)
  have hD0 : D 0 = 1 := by
    dsimp [D]
    simp
  have hW0 : W 0 = 0 := by
    dsimp [W]
    simp
  have hIcc : ∀ k : ℕ,
      Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert (-((k + 1 : ℕ) : ℤ)) (insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ))) := by
    intro k
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotMem1 : ∀ k : ℕ,
      -((k + 1 : ℕ) : ℤ) ∉ insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
    intro k
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotMem2 : ∀ k : ℕ, ((k + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
    intro k
    simp only [Finset.mem_Icc]
    omega
  have hD_step : ∀ k : ℕ, D (k + 1) = D k + 2 * Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u) := by
    intro k
    change (∑ a ∈ Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * u)) =
      (∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * u)) +
        2 * Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u)
    rw [hIcc k, Finset.sum_insert (hnotMem1 k), Finset.sum_insert (hnotMem2 k)]
    have h_neg_cos : Real.cos (2 * Real.pi * ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) * u) =
        Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u) := by
      have h_arg : 2 * Real.pi * ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) * u =
          - (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u) := by push_cast; ring
      rw [h_arg, Real.cos_neg]
    have h_pos_cos : Real.cos (2 * Real.pi * ((((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) * u) =
        Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u) := by
      push_cast; rfl
    rw [h_neg_cos, h_pos_cos]
    ring
  have hW_step : ∀ k : ℕ, W (k + 1) = W k + D k := by
    intro k
    change (∑ a ∈ Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ),
        (((k + 1 : ℕ) : ℝ) - |(a : ℝ)|) * Real.cos (2 * Real.pi * (a : ℝ) * u)) =
      (∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ((k : ℝ) - |(a : ℝ)|) * Real.cos (2 * Real.pi * (a : ℝ) * u)) +
      (∑ a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * u))
    rw [hIcc k, Finset.sum_insert (hnotMem1 k), Finset.sum_insert (hnotMem2 k)]
    have h_abs_neg : |((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)| = ((k + 1 : ℕ) : ℝ) := by
      have h1 : ((-((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) = -(((k + 1 : ℕ) : ℝ)) := by push_cast; ring
      rw [h1, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    have h_abs_pos : |((((k + 1 : ℕ) : ℤ) : ℤ) : ℝ)| = ((k + 1 : ℕ) : ℝ) := by
      have h1 : ((((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h1, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [h_abs_neg, h_abs_pos, sub_self, zero_mul, zero_add, zero_mul, zero_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    ring
  have hD_trig : ∀ k : ℕ, Real.sin (Real.pi * u) * D k = Real.sin ((2 * (k : ℝ) + 1) * Real.pi * u) := by
    intro k
    induction k with
    | zero =>
      rw [hD0]
      push_cast
      have h_arg : (2 * (0 : ℝ) + 1) * Real.pi * u = Real.pi * u := by ring
      rw [h_arg, mul_one]
    | succ k ih =>
      rw [hD_step k, mul_add, ih]
      let x := 2 * ((k + 1 : ℕ) : ℝ) * Real.pi * u
      let y := Real.pi * u
      have h_arg1 : (2 * (k : ℝ) + 1) * Real.pi * u = x - y := by dsimp [x, y]; push_cast; ring
      have h_arg2 : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u = x := by dsimp [x]; ring
      have h_arg3 : (2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.pi * u = x + y := by dsimp [x, y]; ring
      rw [h_arg1, h_arg2, h_arg3]
      change Real.sin (x - y) + y.sin * (2 * Real.cos x) = Real.sin (x + y)
      rw [Real.sin_sub, Real.sin_add]
      ring
  have hW_trig : ∀ k : ℕ, (Real.sin (Real.pi * u)) ^ 2 * W k = (Real.sin ((k : ℝ) * Real.pi * u)) ^ 2 := by
    intro k
    induction k with
    | zero =>
      rw [hW0]
      simp
    | succ k ih =>
      have h1 : (Real.sin (Real.pi * u)) ^ 2 * W (k + 1) =
          (Real.sin (Real.pi * u)) ^ 2 * W k + Real.sin (Real.pi * u) * (Real.sin (Real.pi * u) * D k) := by
        rw [hW_step k]
        ring
      rw [h1, ih, hD_trig k]
      let A := ((k + 1 : ℕ) : ℝ) * Real.pi * u
      let B := (k : ℝ) * Real.pi * u
      have h_sub_arg : Real.pi * u = A - B := by dsimp [A, B]; push_cast; ring
      have h_add_arg : (2 * (k : ℝ) + 1) * Real.pi * u = A + B := by dsimp [A, B]; push_cast; ring
      change (Real.sin B) ^ 2 + Real.sin (Real.pi * u) * Real.sin ((2 * (k : ℝ) + 1) * Real.pi * u) = (Real.sin A) ^ 2
      rw [h_sub_arg, h_add_arg]
      calc (Real.sin B) ^ 2 + Real.sin (A - B) * Real.sin (A + B)
          = (Real.sin B) ^ 2 + (Real.sin A * Real.cos B - Real.cos A * Real.sin B) *
              (Real.sin A * Real.cos B + Real.cos A * Real.sin B) := by
            rw [Real.sin_sub, Real.sin_add]
        _ = (Real.sin A) ^ 2 * ((Real.sin B) ^ 2 + (Real.cos B) ^ 2) +
              (Real.sin B) ^ 2 * (1 - ((Real.sin A) ^ 2 + (Real.cos A) ^ 2)) := by ring
        _ = (Real.sin A) ^ 2 * 1 + (Real.sin B) ^ 2 * (1 - 1) := by
            rw [Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq A]
        _ = (Real.sin A) ^ 2 := by ring
  have hW_nonneg : ∀ k : ℕ, 0 ≤ W k := by
    intro k
    by_cases hsin : Real.sin (Real.pi * u) = 0
    · have hcos2 : Real.cos (2 * Real.pi * u) = 1 := by
        have h_arg : 2 * Real.pi * u = Real.pi * u + Real.pi * u := by ring
        have h_sq := Real.sin_sq_add_cos_sq (Real.pi * u)
        rw [h_arg, Real.cos_add, hsin] at *
        linarith
      have hsin2 : Real.sin (2 * Real.pi * u) = 0 := by
        have h_arg : 2 * Real.pi * u = Real.pi * u + Real.pi * u := by ring
        rw [h_arg, Real.sin_add, hsin]
        ring
      have h_cos_sin : ∀ n : ℕ, Real.cos (2 * Real.pi * (n : ℝ) * u) = 1 ∧ Real.sin (2 * Real.pi * (n : ℝ) * u) = 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have h_arg : 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * u = 2 * Real.pi * (n : ℝ) * u + 2 * Real.pi * u := by
            push_cast; ring
          rw [h_arg, Real.cos_add, Real.sin_add, ih.1, ih.2, hcos2, hsin2]
          simp
      have hD_nonneg : ∀ n : ℕ, 0 ≤ D n := by
        intro n
        induction n with
        | zero => rw [hD0]; norm_num
        | succ n ih =>
          rw [hD_step n, (h_cos_sin (n + 1)).1]
          linarith
      induction k with
      | zero => rw [hW0]
      | succ n ih =>
        rw [hW_step n]
        linarith [hD_nonneg n]
    · have hpos : 0 < (Real.sin (Real.pi * u)) ^ 2 := sq_pos_of_ne_zero hsin
      have hsq : 0 ≤ (Real.sin (Real.pi * u)) ^ 2 * W k := by
        rw [hW_trig k]
        exact sq_nonneg _
      exact nonneg_of_mul_nonneg_right hsq hpos
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hF_eq : (∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (1 - |(a : ℝ)| / (m : ℝ)) * Real.cos (2 * Real.pi * (a : ℝ) * u)) = W m / (m : ℝ) := by
    dsimp [W]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    have h_coeff : (1 - |(a : ℝ)| / (m : ℝ)) = ((m : ℝ) - |(a : ℝ)|) / (m : ℝ) := by
      rw [sub_div, div_self hm_ne]
    rw [h_coeff, div_mul_eq_mul_div]
  constructor
  · rw [hF_eq]
    exact div_nonneg (hW_nonneg m) (le_of_lt hm_pos)
  · intro δ hδ_pos hδ_q hδ_u1 hδ_u2
    rw [hF_eq]
    let v := -u
    have hv1 : δ ≤ v := hδ_u1
    have hv2 : v ≤ 1 - δ := hδ_u2
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have h_sin_delta_pos : 0 < Real.sin (Real.pi * δ) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · exact mul_pos hpi_pos hδ_pos
      · nlinarith
    have h_sin_le : Real.sin (Real.pi * δ) ≤ Real.sin (Real.pi * v) := by
      by_cases hv_half : v ≤ 1 / 2
      · apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · nlinarith
        · nlinarith
        · nlinarith
      · have h_step : Real.sin (Real.pi * δ) ≤ Real.sin (Real.pi * (1 - v)) := by
          apply Real.sin_le_sin_of_le_of_le_pi_div_two
          · nlinarith
          · nlinarith
          · nlinarith
        have h_symm : Real.sin (Real.pi * (1 - v)) = Real.sin (Real.pi * v) := by
          have h_arg : Real.pi * (1 - v) = Real.pi - Real.pi * v := by ring
          rw [h_arg, Real.sin_pi_sub]
        rwa [h_symm] at h_step
    have h_sin_sq_le : (Real.sin (Real.pi * δ)) ^ 2 ≤ (Real.sin (Real.pi * u)) ^ 2 := by
      have h_v_u : (Real.sin (Real.pi * v)) ^ 2 = (Real.sin (Real.pi * u)) ^ 2 := by
        have h_arg : Real.pi * v = - (Real.pi * u) := by dsimp [v]; ring
        rw [h_arg, Real.sin_neg, neg_sq]
      rw [← h_v_u]
      nlinarith
    have h_denom_pos : 0 < (m : ℝ) * (Real.sin (Real.pi * δ)) ^ 2 :=
      mul_pos hm_pos (sq_pos_of_pos h_sin_delta_pos)
    rw [div_le_div_iff₀ hm_pos h_denom_pos]
    calc W m * ((m : ℝ) * (Real.sin (Real.pi * δ)) ^ 2)
        = (m : ℝ) * ((Real.sin (Real.pi * δ)) ^ 2 * W m) := by ring
      _ ≤ (m : ℝ) * ((Real.sin (Real.pi * u)) ^ 2 * W m) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hm_pos)
          exact mul_le_mul_of_nonneg_right h_sin_sq_le (hW_nonneg m)
      _ = (m : ℝ) * (Real.sin ((m : ℝ) * Real.pi * u)) ^ 2 := by
          rw [hW_trig m]
      _ ≤ (m : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left (Real.sin_sq_le_one _) (le_of_lt hm_pos)
      _ = 1 * (m : ℝ) := by ring

theorem rational_grid_fejer_peak_existence (l₀ m : ℕ) (C_m : ℚ) (r : Fin l₀ → ℝ)
    (hm : 1 ≤ m) (hCm : 0 < C_m)
    (h_kern : ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)|) ≤ (C_m : ℝ))
    (hG_nonneg : ∀ x : ℝ,
      0 ≤ ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (1 - |(a : ℝ)| / (m : ℝ)) *
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x)) *
          ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i))
    (hG_ext : ∀ x : ℝ,
      1 / 100 + 1 / (400 * (Nat.ceil C_m + 1) : ℝ) ≤ x →
      x ≤ 1 - 1 / (400 * (Nat.ceil C_m + 1) : ℝ) →
      ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (1 - |(a : ℝ)| / (m : ℝ)) *
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x)) *
          ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i) ≤ 1 / 8) :
    ∃ x_d : ℚ, 0 < x_d ∧ x_d < 1 / 100 ∧
      20 ≤ ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (1 - |(a : ℝ)| / (m : ℝ)) *
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ))) *
          ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i) :=
by
  classical
  
  have h_vanish : ∀ (Q : ℕ) (a : ℤ) (θ : ℝ),
      0 < |a| → |a| < (Q : ℤ) →
      ∑ k ∈ Finset.range Q, Real.cos (θ - 2 * Real.pi * (a : ℝ) * (k : ℝ) / (Q : ℝ)) = 0 := by
    intro Q a θ ha_pos ha_lt
    have hQ_pos : 0 < Q := by omega
    have hQ_r_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ_pos
    have hQ_ne : (Q : ℝ) ≠ 0 := ne_of_gt hQ_r_pos
    let α : ℝ := Real.pi * (a : ℝ) / (Q : ℝ)
    let β : ℕ → ℝ := fun k => θ - 2 * Real.pi * (a : ℝ) * (k : ℝ) / (Q : ℝ)
    let f : ℕ → ℝ := fun k => Real.sin (θ + α - 2 * Real.pi * (a : ℝ) * (k : ℝ) / (Q : ℝ))
    have h_step : ∀ k : ℕ, f k - f (k + 1) = 2 * Real.sin α * Real.cos (β k) := by
      intro k
      have h_arg1 : θ + α - 2 * Real.pi * (a : ℝ) * (k : ℝ) / (Q : ℝ) = β k + α := by
        dsimp [β]; ring
      have h_arg2 : θ + α - 2 * Real.pi * (a : ℝ) * ((k + 1 : ℕ) : ℝ) / (Q : ℝ) = β k - α := by
        dsimp [β, α]; push_cast; ring
      dsimp [f]
      rw [h_arg1, h_arg2, Real.sin_add (β k) α, Real.sin_sub (β k) α]
      ring
    have h_tele : 2 * Real.sin α * ∑ k ∈ Finset.range Q, Real.cos (β k) = f 0 - f Q := by
      rw [Finset.mul_sum]
      have h_congr : (∑ k ∈ Finset.range Q, 2 * Real.sin α * Real.cos (β k)) =
          ∑ k ∈ Finset.range Q, (f k - f (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact (h_step k).symm
      rw [h_congr]
      exact Finset.sum_range_sub' f Q
    have hf_eq : f 0 = f Q := by
      dsimp [f]
      have h0 : θ + α - 2 * Real.pi * (a : ℝ) * ((0 : ℕ) : ℝ) / (Q : ℝ) = θ + α := by
        push_cast; ring
      have hQ_arg : θ + α - 2 * Real.pi * (a : ℝ) * (Q : ℝ) / (Q : ℝ) =
          (θ + α) - (a : ℝ) * (2 * Real.pi) := by
        rw [mul_div_cancel_right₀ _ hQ_ne]
        ring
      rw [h0, hQ_arg, Real.sin_sub_int_mul_two_pi]
    have h_prod_zero : 2 * Real.sin α * ∑ k ∈ Finset.range Q, Real.cos (β k) = 0 := by
      rw [h_tele, hf_eq, sub_self]
    have h_sin_ne : Real.sin α ≠ 0 := by
      have ha_abs_pos : (0 : ℝ) < |(a : ℝ)| := by exact_mod_cast ha_pos
      have ha_abs_lt : |(a : ℝ)| < (Q : ℝ) := by exact_mod_cast ha_lt
      have h_angle_pos : 0 < Real.pi * |(a : ℝ)| / (Q : ℝ) := by positivity
      have h_angle_lt_pi : Real.pi * |(a : ℝ)| / (Q : ℝ) < Real.pi := by
        rw [div_lt_iff₀ hQ_r_pos]
        nlinarith [Real.pi_pos]
      have h_sin_abs_pos : 0 < Real.sin (Real.pi * |(a : ℝ)| / (Q : ℝ)) :=
        Real.sin_pos_of_pos_of_lt_pi h_angle_pos h_angle_lt_pi
      rcases lt_trichotomy (a : ℝ) 0 with ha_neg | ha_zero | ha_pos_r
      · have h_abs : |(a : ℝ)| = -(a : ℝ) := abs_of_neg ha_neg
        have h_alpha_eq : α = - (Real.pi * |(a : ℝ)| / (Q : ℝ)) := by
          dsimp [α]; rw [h_abs]; ring
        rw [h_alpha_eq, Real.sin_neg]
        linarith
      · exfalso
        rw [ha_zero, abs_zero] at ha_abs_pos
        linarith
      · have h_abs : |(a : ℝ)| = (a : ℝ) := abs_of_pos ha_pos_r
        have h_alpha_eq : α = Real.pi * |(a : ℝ)| / (Q : ℝ) := by
          dsimp [α]; rw [h_abs]
        rw [h_alpha_eq]
        linarith
    have h_two_sin_ne : 2 * Real.sin α ≠ 0 := mul_ne_zero two_ne_zero h_sin_ne
    exact (mul_eq_zero.mp h_prod_zero).resolve_left h_two_sin_ne

  
  let K : ℕ := Nat.ceil C_m
  have hK_ge1 : 1 ≤ K := Nat.ceil_pos.mpr hCm
  have hCm_le_K : (C_m : ℝ) ≤ (K : ℝ) := by
    have h_q : C_m ≤ (K : ℚ) := Nat.le_ceil C_m
    exact_mod_cast h_q
  let D : ℕ := 400 * (K + 1)
  let Q : ℕ := D * (m + 1)
  let N_δ : ℕ := m + 1
  let N_100 : ℕ := 4 * (K + 1) * (m + 1)
  have hm_lt_Q : m < Q := by
    dsimp [Q, D]
    nlinarith
  have hQ_pos : 0 < Q := by omega
  have hQ_r_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ_pos
  have hD_pos : 0 < D := by dsimp [D]; omega
  have hD_r_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD_pos
  have hm_r_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)

  let G : ℝ → ℝ := fun x =>
    ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (1 - |(a : ℝ)| / (m : ℝ)) *
        Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x)) *
        ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)

  have h_grid_sum : ∑ k ∈ Finset.Ico 0 Q, G ((k : ℝ) / (Q : ℝ)) = (Q : ℝ) := by
    rw [Nat.Ico_zero_eq_range]
    dsimp [G]
    rw [Finset.sum_comm]
    have h_inner : ∀ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (∑ k ∈ Finset.range Q,
          (1 - |(a : ℝ)| / (m : ℝ)) *
            Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * ((k : ℝ) / (Q : ℝ)))) *
            ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)) =
        (1 - |(a : ℝ)| / (m : ℝ)) * (∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)) *
          ∑ k ∈ Finset.range Q,
            Real.cos (Real.pi * (a : ℝ) * (∑ i : Fin l₀, r i) -
              2 * Real.pi * (a : ℝ) * (k : ℝ) / (Q : ℝ)) := by
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have h_arg : Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * ((k : ℝ) / (Q : ℝ))) =
          Real.pi * (a : ℝ) * (∑ i : Fin l₀, r i) - 2 * Real.pi * (a : ℝ) * (k : ℝ) / (Q : ℝ) := by
        ring
      rw [h_arg]
      ring
    rw [Finset.sum_congr rfl h_inner]
    rw [Finset.sum_eq_single (0 : ℤ)]
    · simp
    · intro a ha ha_ne
      rw [Finset.mem_Icc] at ha
      have ha_abs_pos : 0 < |a| := abs_pos.mpr ha_ne
      have ha_abs_lt : |a| < (Q : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      rw [h_vanish Q a (Real.pi * (a : ℝ) * (∑ i : Fin l₀, r i)) ha_abs_pos ha_abs_lt]
      ring
    · intro h0_not_mem
      exfalso
      apply h0_not_mem
      rw [Finset.mem_Icc]
      omega

  have hG_upper : ∀ x : ℝ, G x ≤ (K + 1 : ℝ) := by
    intro x
    have h_term : ∀ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (1 - |(a : ℝ)| / (m : ℝ)) *
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x)) *
          (∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)) ≤
        ∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)| := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha_abs : |(a : ℝ)| ≤ (m : ℝ) := by
        rw [abs_le]
        constructor <;> exact_mod_cast (by omega)
      have hw_nonneg : 0 ≤ 1 - |(a : ℝ)| / (m : ℝ) := by
        have : |(a : ℝ)| / (m : ℝ) ≤ 1 := (div_le_one hm_r_pos).mpr ha_abs
        linarith
      have hw_le1 : 1 - |(a : ℝ)| / (m : ℝ) ≤ 1 := by
        have : 0 ≤ |(a : ℝ)| / (m : ℝ) := div_nonneg (abs_nonneg _) (le_of_lt hm_r_pos)
        linarith
      have h_abs_term : (1 - |(a : ℝ)| / (m : ℝ)) *
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x)) *
          (∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)) ≤
          |(1 - |(a : ℝ)| / (m : ℝ)) *
            Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x)) *
            (∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i))| := le_abs_self _
      rw [abs_mul, abs_mul, abs_of_nonneg hw_nonneg, Finset.abs_prod] at h_abs_term
      have h_prod_nonneg : 0 ≤ ∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)| :=
        Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      have h_wcos_le1 : (1 - |(a : ℝ)| / (m : ℝ)) *
          |Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x))| ≤ 1 := by
        calc (1 - |(a : ℝ)| / (m : ℝ)) *
              |Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x))|
            ≤ 1 * 1 := mul_le_mul hw_le1 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
          _ = 1 := mul_one 1
      calc (1 - |(a : ℝ)| / (m : ℝ)) *
            Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x)) *
            (∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i))
          ≤ (1 - |(a : ℝ)| / (m : ℝ)) *
            |Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * x))| *
            (∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)|) := h_abs_term
        _ ≤ 1 * (∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)|) :=
            mul_le_mul_of_nonneg_right h_wcos_le1 h_prod_nonneg
        _ = ∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)| := one_mul _
    calc G x
        ≤ ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
            ∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)| := Finset.sum_le_sum h_term
      _ ≤ (C_m : ℝ) := h_kern
      _ ≤ (K : ℝ) := hCm_le_K
      _ ≤ (K + 1 : ℝ) := by linarith

  
  have h_ineq1 : 2 * N_δ < N_100 :=
    (Nat.mul_lt_mul_right (by omega)).mpr (by omega)
  have h_ineq2 : N_100 + 2 * N_δ ≤ Q := by
    have h1 : (4 * (K + 1) + 2) * (m + 1) ≤ 400 * (K + 1) * (m + 1) :=
      Nat.mul_le_mul_right (m + 1) (by omega)
    have h2 : N_100 + 2 * N_δ = (4 * (K + 1) + 2) * (m + 1) := by
      dsimp [N_100, N_δ]; ring
    rw [h2]
    exact h1
  have h_ord1 : 0 ≤ N_δ := by omega
  have h_ord2 : N_δ ≤ N_100 - N_δ := by omega
  have h_ord3 : N_100 - N_δ ≤ N_100 + N_δ := by omega
  have h_ord4 : N_100 + N_δ ≤ Q - N_δ := by omega
  have h_ord5 : Q - N_δ ≤ Q := by omega
  have h_I2_lt : N_δ < N_100 - N_δ := by omega

  let g : ℕ → ℝ := fun k => G ((k : ℝ) / (Q : ℝ))
  let S1 := ∑ k ∈ Finset.Ico 0 N_δ, g k
  let S2 := ∑ k ∈ Finset.Ico N_δ (N_100 - N_δ), g k
  let S3 := ∑ k ∈ Finset.Ico (N_100 - N_δ) (N_100 + N_δ), g k
  let S4 := ∑ k ∈ Finset.Ico (N_100 + N_δ) (Q - N_δ), g k
  let S5 := ∑ k ∈ Finset.Ico (Q - N_δ) Q, g k

  have h_split12 : S1 + S2 = ∑ k ∈ Finset.Ico 0 (N_100 - N_δ), g k :=
    Finset.sum_Ico_consecutive g h_ord1 h_ord2
  have h_split123 : (∑ k ∈ Finset.Ico 0 (N_100 - N_δ), g k) + S3 =
      ∑ k ∈ Finset.Ico 0 (N_100 + N_δ), g k :=
    Finset.sum_Ico_consecutive g (le_trans h_ord1 h_ord2) h_ord3
  have h_split1234 : (∑ k ∈ Finset.Ico 0 (N_100 + N_δ), g k) + S4 =
      ∑ k ∈ Finset.Ico 0 (Q - N_δ), g k :=
    Finset.sum_Ico_consecutive g (le_trans (le_trans h_ord1 h_ord2) h_ord3) h_ord4
  have h_split12345 : (∑ k ∈ Finset.Ico 0 (Q - N_δ), g k) + S5 =
      ∑ k ∈ Finset.Ico 0 Q, g k :=
    Finset.sum_Ico_consecutive g (le_trans (le_trans (le_trans h_ord1 h_ord2) h_ord3) h_ord4) h_ord5
  have h_total_eq : S1 + S2 + S3 + S4 + S5 = (Q : ℝ) := by
    rw [h_split12, h_split123, h_split1234, h_split12345, h_grid_sum]

  have h_bound_Ico : ∀ a b : ℕ, ∑ k ∈ Finset.Ico a b, g k ≤ ((b - a : ℕ) : ℝ) * (K + 1 : ℝ) := by
    intro a b
    have h_le := Finset.sum_le_card_nsmul (Finset.Ico a b) g (K + 1 : ℝ) (fun k _ => hG_upper ((k : ℝ) / (Q : ℝ)))
    rw [Nat.card_Ico, nsmul_eq_mul] at h_le
    exact h_le

  have hS1_le : S1 ≤ (N_δ : ℝ) * (K + 1 : ℝ) := by
    have h_b := h_bound_Ico 0 N_δ
    rwa [Nat.sub_zero] at h_b
  have hS3_le : S3 ≤ (2 * N_δ : ℝ) * (K + 1 : ℝ) := by
    have h_sub : N_100 + N_δ - (N_100 - N_δ) = 2 * N_δ := by omega
    have h_b := h_bound_Ico (N_100 - N_δ) (N_100 + N_δ)
    rw [h_sub] at h_b
    push_cast at h_b
    exact h_b
  have hS5_le : S5 ≤ (N_δ : ℝ) * (K + 1 : ℝ) := by
    have h_sub : Q - (Q - N_δ) = N_δ := by omega
    have h_b := h_bound_Ico (Q - N_δ) Q
    rwa [h_sub] at h_b
  have h_buf_le : S1 + S3 + S5 ≤ (Q : ℝ) / 100 := by
    have h_Q_eq : (Q : ℝ) = 400 * (K + 1 : ℝ) * (N_δ : ℝ) := by
      dsimp [Q, D, N_δ]
      push_cast
      ring
    linarith

  have hS4_le : S4 ≤ (Q : ℝ) / 8 := by
    have h_ext_I4 : ∀ k ∈ Finset.Ico (N_100 + N_δ) (Q - N_δ), g k ≤ 1 / 8 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : (N_100 : ℝ) + (N_δ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      have hk2 : (k : ℝ) ≤ (Q : ℝ) - (N_δ : ℝ) := by
        have hk2_nat : k + N_δ ≤ Q := by omega
        have hk2_r : (k : ℝ) + (N_δ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hk2_nat
        linarith
      have h_N100_eq : (N_100 : ℝ) / (Q : ℝ) = 1 / 100 := by
        dsimp [N_100, Q, D]
        push_cast
        have h_denom : (400 * ((K : ℝ) + 1) * ((m : ℝ) + 1)) ≠ 0 := by positivity
        field_simp
        ring
      have h_Nδ_eq : (N_δ : ℝ) / (Q : ℝ) = 1 / (400 * ((K : ℝ) + 1)) := by
        dsimp [N_δ, Q, D]
        push_cast
        have hm1_ne : (m : ℝ) + 1 ≠ 0 := by positivity
        have hK1_ne : 400 * ((K : ℝ) + 1) ≠ 0 := by positivity
        field_simp
      have hx_low : 1 / 100 + 1 / (400 * (Nat.ceil C_m + 1) : ℝ) ≤ (k : ℝ) / (Q : ℝ) := by
        have h_div : ((N_100 : ℝ) + (N_δ : ℝ)) / (Q : ℝ) ≤ (k : ℝ) / (Q : ℝ) :=
          div_le_div_of_nonneg_right hk1 (le_of_lt hQ_r_pos)
        rw [add_div, h_N100_eq, h_Nδ_eq] at h_div
        simpa [K] using h_div
      have hx_high : (k : ℝ) / (Q : ℝ) ≤ 1 - 1 / (400 * (Nat.ceil C_m + 1) : ℝ) := by
        have h_div : (k : ℝ) / (Q : ℝ) ≤ ((Q : ℝ) - (N_δ : ℝ)) / (Q : ℝ) :=
          div_le_div_of_nonneg_right hk2 (le_of_lt hQ_r_pos)
        rw [sub_div, div_self (ne_of_gt hQ_r_pos), h_Nδ_eq] at h_div
        simpa [K] using h_div
      exact hG_ext ((k : ℝ) / (Q : ℝ)) hx_low hx_high
    have h_card_le : ((Finset.Ico (N_100 + N_δ) (Q - N_δ)).card : ℝ) ≤ (Q : ℝ) := by
      rw [Nat.card_Ico]
      have h_le_nat : Q - N_δ - (N_100 + N_δ) ≤ Q := by omega
      exact_mod_cast h_le_nat
    have h_sum_I4 := Finset.sum_le_card_nsmul (Finset.Ico (N_100 + N_δ) (Q - N_δ)) g (1 / 8 : ℝ) h_ext_I4
    rw [nsmul_eq_mul] at h_sum_I4
    calc S4 ≤ ((Finset.Ico (N_100 + N_δ) (Q - N_δ)).card : ℝ) * (1 / 8 : ℝ) := h_sum_I4
      _ ≤ (Q : ℝ) * (1 / 8 : ℝ) := mul_le_mul_of_nonneg_right h_card_le (by norm_num)
      _ = (Q : ℝ) / 8 := by ring

  have hS2_ge : (173 / 200 : ℝ) * (Q : ℝ) ≤ S2 := by linarith
  have h_sum20_le : ∑ _k ∈ Finset.Ico N_δ (N_100 - N_δ), (20 : ℝ) ≤ S2 := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    have h_card2_le : ((N_100 - N_δ - N_δ : ℕ) : ℝ) ≤ (N_100 : ℝ) := by
      exact_mod_cast (by omega : N_100 - N_δ - N_δ ≤ N_100)
    have h_N100_Q : (N_100 : ℝ) * 20 = (40 / 200 : ℝ) * (Q : ℝ) := by
      dsimp [N_100, Q, D]
      push_cast
      ring
    nlinarith

  have hI2_nonempty : (Finset.Ico N_δ (N_100 - N_δ)).Nonempty :=
    Finset.nonempty_Ico.mpr h_I2_lt
  obtain ⟨k₀, hk₀_mem, hk₀_ge20⟩ := Finset.exists_le_of_sum_le hI2_nonempty h_sum20_le
  rw [Finset.mem_Ico] at hk₀_mem
  let x_d : ℚ := (k₀ : ℚ) / (Q : ℚ)
  have hQ_q_pos : (0 : ℚ) < (Q : ℚ) := Nat.cast_pos.mpr hQ_pos
  have hk₀_pos : 0 < k₀ := by omega
  have hk₀_lt_N100 : k₀ < N_100 := by omega
  have hxd_pos : 0 < x_d := div_pos (Nat.cast_pos.mpr hk₀_pos) hQ_q_pos
  have hxd_lt : x_d < 1 / 100 := by
    dsimp [x_d]
    rw [div_lt_div_iff₀ hQ_q_pos (by norm_num)]
    have hk₀_q : (k₀ : ℚ) * 100 < (Q : ℚ) * 1 := by
      have h_nat : k₀ * 100 < Q * 1 := by
        have h_Q100 : 100 * N_100 = Q := by dsimp [Q, D, N_100]; ring
        omega
      exact_mod_cast h_nat
    linarith
  refine ⟨x_d, hxd_pos, hxd_lt, ?_⟩
  have h_cast_xd : (x_d : ℝ) = (k₀ : ℝ) / (Q : ℝ) := by
    dsimp [x_d]
    push_cast
    rfl
  rw [h_cast_xd]
  exact hk₀_ge20

theorem fejer_limit_density_and_low_freq_positivity (B : ℕ) (C_m : ℚ) (l_seq : ℕ → ℕ) (I_seq : ℕ → ℕ × ℕ)
    (hB : 1189 ≤ B) (hCm : 0 < C_m)
    (h_mono : 1 ≤ l_seq B ∧ ∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → l_seq Y₁ ≤ l_seq Y₂)
    (h_bounds : ∀ k : ℕ, 495 ≤ (I_seq k).1 ∧ (I_seq k).1 < (I_seq k).2 ∧ (I_seq k).2 ≤ (I_seq k).1 + 2)
    (h_mass : ∀ n : ℕ, ∑ k ∈ Finset.range n, w_Icc (I_seq k).1 (I_seq k).2 ≤ 1 / 118900)
    (h_kern : ∀ Y ≥ B,
      ∑ a ∈ Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2) ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1),
        Real.exp (- (1 / 3 : ℝ) * ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2) ≤ (C_m : ℝ)) :
    ∃ (x_d g₀ : ℚ) (A₀ : ℕ),
      0 < x_d ∧ x_d < 1 / 100 ∧ 0 < g₀ ∧ 1 ≤ A₀ ∧
      ∀ H₀ : ℕ, A₀ ≤ H₀ → ∃ Y_low : ℕ, B ≤ Y_low ∧
        ∀ Y ≥ Y_low,
          3 / 4 * (g₀ : ℝ) ≤
            ∑ a ∈ Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ),
              Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin (l_seq Y), (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ))) - 2 * (x_d : ℝ))) *
                ∏ i : Fin (l_seq Y), Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ))) :=
by
  classical
  have reserve_subset_cosine_product_identity : ∀ (l₀ : ℕ) (r : Fin l₀ → ℝ) (θ₀ : ℝ) (a : ℤ),
      ((1 / 2 : ℝ) ^ l₀) *
        ∑ S ∈ (Finset.univ : Finset (Fin l₀)).powerset,
          Real.cos (θ₀ + 2 * Real.pi * (a : ℝ) * ∑ i ∈ S, r i) =
      Real.cos (θ₀ + Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i) *
        ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i) := by
    intro l₀ r θ₀ a
    let α : Fin l₀ → ℝ := fun i => Real.pi * (a : ℝ) * r i
    have h_ind : ∀ (U : Finset (Fin l₀)) (θ : ℝ),
        ((1 / 2 : ℝ) ^ U.card) *
          ∑ S ∈ U.powerset, Real.cos (θ + 2 * ∑ i ∈ S, α i) =
        Real.cos (θ + ∑ i ∈ U, α i) * ∏ i ∈ U, Real.cos (α i) := by
      intro U
      induction U using Finset.induction_on with
      | empty =>
        intro θ
        simp
      | @insert j V hj ih =>
        intro θ
        rw [Finset.card_insert_of_notMem hj, Finset.sum_powerset_insert hj,
          Finset.sum_insert hj, Finset.prod_insert hj]
        have h_shift : (∑ t ∈ V.powerset, Real.cos (θ + 2 * ∑ i ∈ insert j t, α i)) =
            ∑ t ∈ V.powerset, Real.cos ((θ + 2 * α j) + 2 * ∑ i ∈ t, α i) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hjt : j ∉ t := fun h_mem => hj (Finset.mem_powerset.mp ht h_mem)
          rw [Finset.sum_insert hjt]
          ring_nf
        rw [h_shift, pow_succ, mul_comm ((1 / 2 : ℝ) ^ V.card) (1 / 2 : ℝ), mul_assoc, mul_add,
          ih θ, ih (θ + 2 * α j)]
        let ψ := θ + α j + ∑ i ∈ V, α i
        have h_arg1 : θ + ∑ i ∈ V, α i = ψ - α j := by dsimp [ψ]; ring
        have h_arg2 : θ + 2 * α j + ∑ i ∈ V, α i = ψ + α j := by dsimp [ψ]; ring
        have h_arg3 : θ + (α j + ∑ i ∈ V, α i) = ψ := by dsimp [ψ]; ring
        rw [h_arg1, h_arg2, h_arg3]
        have h_trig : (1 / 2 : ℝ) * (Real.cos (ψ - α j) * ∏ i ∈ V, Real.cos (α i) +
            Real.cos (ψ + α j) * ∏ i ∈ V, Real.cos (α i)) =
            Real.cos ψ * (Real.cos (α j) * ∏ i ∈ V, Real.cos (α i)) := by
          rw [Real.cos_sub ψ (α j), Real.cos_add ψ (α j)]
          ring
        exact h_trig
    have h_univ := h_ind Finset.univ θ₀
    have h_card : (Finset.univ : Finset (Fin l₀)).card = l₀ := by simp
    have h_sum_lhs : (∑ S ∈ (Finset.univ : Finset (Fin l₀)).powerset,
        Real.cos (θ₀ + 2 * Real.pi * (a : ℝ) * ∑ i ∈ S, r i)) =
        ∑ S ∈ (Finset.univ : Finset (Fin l₀)).powerset,
          Real.cos (θ₀ + 2 * ∑ i ∈ S, α i) := by
      apply Finset.sum_congr rfl
      intro S _
      congr 1
      dsimp [α]
      rw [← Finset.mul_sum]
      ring
    have h_sum_rhs : Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i = ∑ i ∈ (Finset.univ : Finset (Fin l₀)), α i := by
      dsimp [α]
      rw [← Finset.mul_sum]
    rw [h_card] at h_univ
    rw [h_sum_lhs, h_sum_rhs]
    exact h_univ

  have prefix_cosine_product_monotone_and_lipschitz :
      ∀ (r : ℕ → ℝ) (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
        (n₁ n₂ : ℕ) (hn : n₁ ≤ n₂) (a : ℤ) (x : ℝ),
        (|∏ k ∈ Finset.range n₂, Real.cos (Real.pi * (a : ℝ) * r k)| ≤
          |∏ k ∈ Finset.range n₁, Real.cos (Real.pi * (a : ℝ) * r k)|) ∧
        (|∏ k ∈ Finset.range n₁, Real.cos (Real.pi * (a : ℝ) * r k)| ≤
          Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Finset.range n₁, (Real.sin (Real.pi * (a : ℝ) * r k)) ^ 2)) ∧
        (|Real.cos (Real.pi * (a : ℝ) * ((∑ k ∈ Finset.range n₂, r k) - 2 * x)) *
            (∏ k ∈ Finset.range n₂, Real.cos (Real.pi * (a : ℝ) * r k)) -
          Real.cos (Real.pi * (a : ℝ) * ((∑ k ∈ Finset.range n₁, r k) - 2 * x)) *
            (∏ k ∈ Finset.range n₁, Real.cos (Real.pi * (a : ℝ) * r k))| ≤
          4 * |(a : ℝ)| * ((∑ k ∈ Finset.range n₂, r k) - (∑ k ∈ Finset.range n₁, r k))) := by
    intro r hr_nonneg n₁ n₂ hn a x
    have h_prod_le_one : ∀ n : ℕ, |∏ k ∈ Finset.range n, Real.cos (Real.pi * (a : ℝ) * r k)| ≤ 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.prod_range_succ, abs_mul]
        calc |∏ k ∈ Finset.range n, Real.cos (Real.pi * (a : ℝ) * r k)| * |Real.cos (Real.pi * (a : ℝ) * r n)|
            ≤ 1 * 1 := mul_le_mul ih (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
          _ = 1 := mul_one 1
    refine ⟨?_, ?_, ?_⟩
    · induction n₂, hn using Nat.le_induction with
      | base => exact le_rfl
      | succ n h_le ih =>
        rw [Finset.prod_range_succ, abs_mul]
        calc |∏ k ∈ Finset.range n, Real.cos (Real.pi * (a : ℝ) * r k)| * |Real.cos (Real.pi * (a : ℝ) * r n)|
            ≤ |∏ k ∈ Finset.range n, Real.cos (Real.pi * (a : ℝ) * r k)| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
          _ = |∏ k ∈ Finset.range n, Real.cos (Real.pi * (a : ℝ) * r k)| := mul_one _
          _ ≤ |∏ k ∈ Finset.range n₁, Real.cos (Real.pi * (a : ℝ) * r k)| := ih
    · have h_cos_exp : ∀ u : ℝ, |Real.cos u| ≤ Real.exp (- (1 / 3 : ℝ) * (Real.sin u) ^ 2) := by
        intro u
        have h1 : (Real.cos u) ^ 2 ≤ Real.exp (- (2 / 3 : ℝ) * (Real.sin u) ^ 2) := by
          have h_id := Real.sin_sq_add_cos_sq u
          have h_sq : 0 ≤ (Real.sin u) ^ 2 := sq_nonneg _
          have h_exp := Real.add_one_le_exp (- (2 / 3 : ℝ) * (Real.sin u) ^ 2)
          linarith
        have h2 : |Real.cos u| ^ 2 ≤ (Real.exp (- (1 / 3 : ℝ) * (Real.sin u) ^ 2)) ^ 2 := by
          rw [sq_abs, sq (Real.exp _), ← Real.exp_add]
          have h_eq : - (1 / 3 : ℝ) * (Real.sin u) ^ 2 + - (1 / 3 : ℝ) * (Real.sin u) ^ 2 =
              - (2 / 3 : ℝ) * (Real.sin u) ^ 2 := by ring
          rw [h_eq]
          exact h1
        have h3 : 0 ≤ |Real.cos u| := abs_nonneg _
        have h4 : 0 < Real.exp (- (1 / 3 : ℝ) * (Real.sin u) ^ 2) := Real.exp_pos _
        nlinarith
      rw [Finset.abs_prod]
      calc ∏ k ∈ Finset.range n₁, |Real.cos (Real.pi * (a : ℝ) * r k)|
          ≤ ∏ k ∈ Finset.range n₁, Real.exp (- (1 / 3 : ℝ) * (Real.sin (Real.pi * (a : ℝ) * r k)) ^ 2) := by
            apply Finset.prod_le_prod
            · intro k _; exact abs_nonneg _
            · intro k _; exact h_cos_exp _
        _ = Real.exp (∑ k ∈ Finset.range n₁, - (1 / 3 : ℝ) * (Real.sin (Real.pi * (a : ℝ) * r k)) ^ 2) :=
            (Real.exp_sum _ _).symm
        _ = Real.exp (- (1 / 3 : ℝ) * ∑ k ∈ Finset.range n₁, (Real.sin (Real.pi * (a : ℝ) * r k)) ^ 2) := by
            rw [← Finset.mul_sum]
    · induction n₂, hn using Nat.le_induction with
      | base => simp
      | succ n h_le ih =>
        set σ := fun m => ∑ k ∈ Finset.range m, r k
        set φ := fun m => ∏ k ∈ Finset.range m, Real.cos (Real.pi * (a : ℝ) * r k)
        set τ := fun m => Real.cos (Real.pi * (a : ℝ) * (σ m - 2 * x)) * φ m
        have h_step : |τ (n + 1) - τ n| ≤ 4 * |(a : ℝ)| * r n := by
          let θ := Real.pi * (a : ℝ) * (σ n - 2 * x)
          let α := Real.pi * (a : ℝ) * r n
          have hσ_succ : σ (n + 1) = σ n + r n := Finset.sum_range_succ r n
          have hφ_succ : φ (n + 1) = φ n * Real.cos α := Finset.prod_range_succ _ n
          have h_arg : Real.pi * (a : ℝ) * (σ (n + 1) - 2 * x) = θ + α := by
            rw [hσ_succ]; dsimp [θ, α]; ring
          have hτ_diff : τ (n + 1) - τ n = (Real.cos (θ + α) * Real.cos α - Real.cos θ) * φ n := by
            dsimp [τ]
            rw [h_arg, hφ_succ]
            ring
          have h_trig : Real.cos (θ + α) * Real.cos α - Real.cos θ =
              (1 / 2 : ℝ) * (Real.cos (θ + 2 * α) - Real.cos θ) := by
            have h_add : Real.cos (θ + 2 * α) = Real.cos ((θ + α) + α) := by ring_nf
            have h_sub : Real.cos θ = Real.cos ((θ + α) - α) := by ring_nf
            rw [h_add, h_sub, Real.cos_add (θ + α) α, Real.cos_sub (θ + α) α]
            ring
          have h_lip : |Real.cos (θ + α) * Real.cos α - Real.cos θ| ≤ |α| := by
            rw [h_trig, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            have h_c := Real.abs_cos_sub_cos_le (θ + 2 * α) θ
            have h_a : (θ + 2 * α) - θ = 2 * α := by ring
            rw [h_a, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h_c
            linarith
          have h_alpha : |α| ≤ 4 * |(a : ℝ)| * r n := by
            dsimp [α]
            rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (hr_nonneg n)]
            have h_pi : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
            have h_ar : 0 ≤ |(a : ℝ)| * r n := mul_nonneg (abs_nonneg _) (hr_nonneg n)
            nlinarith
          have h_rhs_nonneg : 0 ≤ 4 * |(a : ℝ)| * r n :=
            mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (hr_nonneg n)
          rw [hτ_diff, abs_mul]
          calc |Real.cos (θ + α) * Real.cos α - Real.cos θ| * |φ n|
              ≤ (4 * |(a : ℝ)| * r n) * 1 :=
                mul_le_mul (le_trans h_lip h_alpha) (h_prod_le_one n) (abs_nonneg _) h_rhs_nonneg
            _ = 4 * |(a : ℝ)| * r n := mul_one _
        have h_tri : |τ (n + 1) - τ n₁| ≤ |τ (n + 1) - τ n| + |τ n - τ n₁| :=
          abs_sub_le (τ (n + 1)) (τ n) (τ n₁)
        have h_sum_r : σ (n + 1) - σ n₁ = (σ n - σ n₁) + r n := by
          change (∑ k ∈ Finset.range (n + 1), r k) - σ n₁ = (σ n - σ n₁) + r n
          rw [Finset.sum_range_succ]
          ring
        change |τ (n + 1) - τ n₁| ≤ 4 * |(a : ℝ)| * (σ (n + 1) - σ n₁)
        rw [h_sum_r]
        linarith

  have bounded_monotone_cauchy : ∀ (f : ℕ → ℝ) (M ε : ℝ) (hε : 0 < ε)
      (hf_nonneg : ∀ n : ℕ, 0 ≤ f n) (hf_bound : ∀ n : ℕ, f n ≤ M),
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ n ≥ N₀, f n - f N₀ ≤ ε := by
    intro f M ε hε hf_nonneg hf_bound
    by_contra! h_contra
    let step : {N : ℕ // 1 ≤ N} → {N : ℕ // 1 ≤ N} := fun x =>
      ⟨Classical.choose (h_contra x.1 x.2), le_trans x.2 (Classical.choose_spec (h_contra x.1 x.2)).1⟩
    have h_step_gt : ∀ x : {N : ℕ // 1 ≤ N}, f x.1 + ε < f (step x).1 := by
      intro x
      have hs := (Classical.choose_spec (h_contra x.1 x.2)).2
      linarith
    let seq : ℕ → {N : ℕ // 1 ≤ N} := fun k => step^[k] ⟨1, le_rfl⟩
    have h_seq_ge : ∀ k : ℕ, (k : ℝ) * ε ≤ f (seq k).1 := by
      intro k
      induction k with
      | zero =>
        simp [seq, hf_nonneg]
      | succ k ih =>
        have h_next : seq (k + 1) = step (seq k) := Function.iterate_succ_apply' step k ⟨1, le_rfl⟩
        rw [h_next, Nat.cast_add, Nat.cast_one]
        have h_gt := h_step_gt (seq k)
        linarith
    obtain ⟨K, hK⟩ := exists_nat_gt (M / ε)
    have hK_mul : M < (K : ℝ) * ε := (div_lt_iff₀ hε).mp hK
    have h_le_M : f (seq K).1 ≤ M := hf_bound (seq K).1
    have h_ge_K : (K : ℝ) * ε ≤ f (seq K).1 := h_seq_ge K
    linarith

  have monotone_antitone_tail_stabilization : ∀ (B : ℕ) (C_m : ℝ) (S : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
      (hCm : 0 < C_m)
      (hS : (∀ Y : ℕ, 0 ≤ S Y ∧ S Y ≤ 1 / 100) ∧ (∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → S Y₁ ≤ S Y₂))
      (hU_Y : (∀ Y H : ℕ, 0 ≤ U Y H) ∧ (∀ H Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → U Y₂ H ≤ U Y₁ H))
      (hU_H : ∀ Y H₁ H₂ : ℕ, H₁ ≤ H₂ → U Y H₁ ≤ U Y H₂)
      (hU_bound : ∀ H Y : ℕ, max B (1189 * (2 * H + 2)) ≤ Y → U Y H ≤ C_m),
      ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ m : ℕ, A₀ ≤ m →
        ∃ Y_star : ℕ, max B (1189 * (2 * m + 2)) ≤ Y_star ∧
          U Y_star m - U Y_star A₀ ≤ 2 ∧
          (∀ Y ≥ Y_star, S Y - S Y_star ≤ 1 / (4 * (2 * (A₀ : ℝ) + 1) * (A₀ : ℝ))) ∧
          (∀ H₀ ≥ A₀, ∃ Y_low ≥ Y_star, ∀ Y ≥ Y_low, U Y H₀ - U Y A₀ ≤ 2) := by
    intro B C_m S U hCm hS hU_Y hU_H hU_bound
    let u : ℕ → ℝ := fun H => sInf (Set.range (fun k : ℕ => U (B + k) H))
    have h_bdd : ∀ H : ℕ, BddBelow (Set.range (fun k : ℕ => U (B + k) H)) := by
      intro H
      refine ⟨0, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hU_Y.1 (B + k) H
    have hu_nonneg : ∀ H : ℕ, 0 ≤ u H := by
      intro H
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨k, rfl⟩
      exact hU_Y.1 (B + k) H
    have hu_le_U : ∀ (H Y : ℕ), B ≤ Y → u H ≤ U Y H := by
      intro H Y hY
      apply csInf_le (h_bdd H)
      refine ⟨Y - B, ?_⟩
      dsimp
      have h_eq : B + (Y - B) = Y := by omega
      rw [h_eq]
    have hu_bound : ∀ H : ℕ, u H ≤ C_m := by
      intro H
      let Y₀ := max B (1189 * (2 * H + 2))
      exact le_trans (hu_le_U H Y₀ (le_max_left _ _)) (hU_bound H Y₀ le_rfl)
    obtain ⟨A₀, hA₀_ge1, hA₀_cauchy⟩ :=
      bounded_monotone_cauchy u C_m 1 zero_lt_one hu_nonneg hu_bound
    refine ⟨A₀, hA₀_ge1, fun m hm => ?_⟩
    have h_um_lt : u m < u m + 1 := by linarith
    obtain ⟨_, ⟨k₁, rfl⟩, hk₁⟩ := exists_lt_of_csInf_lt (Set.range_nonempty (fun k : ℕ => U (B + k) m)) h_um_lt
    let ε_S : ℝ := 1 / (4 * (2 * (A₀ : ℝ) + 1) * (A₀ : ℝ))
    have hε_S_pos : 0 < ε_S := by
      have : (1 : ℝ) ≤ (A₀ : ℝ) := by exact_mod_cast hA₀_ge1
      positivity
    obtain ⟨k₂, hk₂_ge1, hk₂_cauchy⟩ :=
      bounded_monotone_cauchy (fun k => S (B + k)) (1 / 100) ε_S hε_S_pos
        (fun k => (hS.1 (B + k)).1) (fun k => (hS.1 (B + k)).2)
    let Y_star := max (max B (1189 * (2 * m + 2))) (max (B + k₁) (B + k₂))
    have hY_star_max : max B (1189 * (2 * m + 2)) ≤ Y_star := le_max_left _ _
    have hY_star_B : B ≤ Y_star := le_trans (le_max_left _ _) hY_star_max
    have hY_star_k₁ : B + k₁ ≤ Y_star := le_trans (le_max_left _ _) (le_max_right _ _)
    have hY_star_k₂ : B + k₂ ≤ Y_star := le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨Y_star, hY_star_max, ?_, ?_, ?_⟩
    · have h1 : U Y_star m ≤ U (B + k₁) m := hU_Y.2 m (B + k₁) Y_star hY_star_k₁
      have h2 : u A₀ ≤ U Y_star A₀ := hu_le_U A₀ Y_star hY_star_B
      have h3 : u m - u A₀ ≤ 1 := hA₀_cauchy m hm
      linarith
    · intro Y hY
      have hY_B : B ≤ Y := le_trans hY_star_B hY
      have h_eq : Y = B + (Y - B) := by omega
      have hk_ge : k₂ ≤ Y - B := by omega
      have h_step := hk₂_cauchy (Y - B) hk_ge
      rw [← h_eq] at h_step
      have h_mono_S : S (B + k₂) ≤ S Y_star := hS.2 (B + k₂) Y_star hY_star_k₂
      linarith
    · intro H₀ hH₀
      have h_uH_lt : u H₀ < u H₀ + 1 := by linarith
      obtain ⟨_, ⟨k₃, rfl⟩, hk₃⟩ := exists_lt_of_csInf_lt (Set.range_nonempty (fun k : ℕ => U (B + k) H₀)) h_uH_lt
      let Y_low := max Y_star (B + k₃)
      refine ⟨Y_low, le_max_left _ _, fun Y hY => ?_⟩
      have hY_k₃ : B + k₃ ≤ Y := le_trans (le_max_right _ _) hY
      have hY_B : B ≤ Y := le_trans hY_star_B (le_trans (le_max_left _ _) hY)
      have h1 : U Y H₀ ≤ U (B + k₃) H₀ := hU_Y.2 H₀ (B + k₃) Y hY_k₃
      have h2 : u A₀ ≤ U Y A₀ := hu_le_U A₀ Y hY_B
      have h3 : u H₀ - u A₀ ≤ 1 := hA₀_cauchy H₀ hH₀
      linarith

  let r : ℕ → ℝ := fun k => 1189 * (w_Icc (I_seq k).1 (I_seq k).2 : ℝ)
  have hr_nonneg : ∀ k : ℕ, 0 ≤ r k := by
    intro k
    dsimp [r]
    have hw : (0 : ℚ) ≤ w_Icc (I_seq k).1 (I_seq k).2 := by
      apply Finset.sum_nonneg
      intro n _
      positivity
    have hw_r : (0 : ℝ) ≤ (w_Icc (I_seq k).1 (I_seq k).2 : ℝ) := by exact_mod_cast hw
    positivity
  let σ : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, r k
  let φ : ℕ → ℤ → ℝ := fun n a => ∏ k ∈ Finset.range n, Real.cos (Real.pi * (a : ℝ) * r k)
  let τ : ℕ → ℤ → ℝ → ℝ := fun n a x => Real.cos (Real.pi * (a : ℝ) * (σ n - 2 * x)) * φ n a
  let S : ℕ → ℝ := fun Y => σ (l_seq Y)
  let U : ℕ → ℕ → ℝ := fun Y H => ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), |φ (l_seq Y) a|
  have hCm_r : (0 : ℝ) < (C_m : ℝ) := Rat.cast_pos.mpr hCm
  have hS_props : (∀ Y : ℕ, 0 ≤ S Y ∧ S Y ≤ 1 / 100) ∧ (∀ Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → S Y₁ ≤ S Y₂) := by
    refine ⟨fun Y => ⟨?_, ?_⟩, fun Y₁ Y₂ hY => ?_⟩
    · exact Finset.sum_nonneg (fun k _ => hr_nonneg k)
    · dsimp [S, σ, r]
      rw [← Finset.mul_sum]
      have hm_q := h_mass (l_seq Y)
      have hm_r : ((∑ k ∈ Finset.range (l_seq Y), w_Icc (I_seq k).1 (I_seq k).2 : ℚ) : ℝ) ≤ ((1 / 118900 : ℚ) : ℝ) := by
        exact_mod_cast hm_q
      push_cast at hm_r
      linarith
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (h_mono.2 Y₁ Y₂ hY)) (fun k _ _ => hr_nonneg k)
  have hU_Y_props : (∀ Y H : ℕ, 0 ≤ U Y H) ∧ (∀ H Y₁ Y₂ : ℕ, Y₁ ≤ Y₂ → U Y₂ H ≤ U Y₁ H) := by
    refine ⟨fun Y H => Finset.sum_nonneg (fun a _ => abs_nonneg _), fun H Y₁ Y₂ hY => ?_⟩
    apply Finset.sum_le_sum
    intro a _
    exact (prefix_cosine_product_monotone_and_lipschitz r hr_nonneg (l_seq Y₁) (l_seq Y₂) (h_mono.2 Y₁ Y₂ hY) a 0).1
  have hU_H_props : ∀ Y H₁ H₂ : ℕ, H₁ ≤ H₂ → U Y H₁ ≤ U Y H₂ := by
    intro Y H₁ H₂ hH
    have h_sub : Finset.Icc (-(H₁ : ℤ)) (H₁ : ℤ) ⊆ Finset.Icc (-(H₂ : ℤ)) (H₂ : ℤ) := by
      intro a ha
      rw [Finset.mem_Icc] at ha ⊢
      omega
    exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun a _ _ => abs_nonneg _)
  have hU_bound : ∀ H Y : ℕ, max B (1189 * (2 * H + 2)) ≤ Y → U Y H ≤ (C_m : ℝ) := by
    intro H Y hY_max
    have hY_B : B ≤ Y := le_trans (le_max_left _ _) hY_max
    have hY_H : 1189 * (2 * H + 2) ≤ Y := le_trans (le_max_right _ _) hY_max
    have hY_ge1 : 1 ≤ Y := by omega
    have hY_mem : Y ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨hY_ge1, le_rfl⟩
    have hY_dvd : Y ∣ (Finset.Icc 1 Y).lcm id := Finset.dvd_lcm hY_mem
    have hlcm_ne : (Finset.Icc 1 Y).lcm id ≠ 0 := by
      rw [ne_eq, Finset.lcm_eq_zero_iff]
      intro h_zero
      rcases h_zero with ⟨x, hx, hx0⟩
      rw [Finset.mem_Icc] at hx
      dsimp at hx0
      omega
    have hY_le_lcm : Y ≤ (Finset.Icc 1 Y).lcm id := Nat.le_of_dvd (Nat.pos_of_ne_zero hlcm_ne) hY_dvd
    have hL_ge : 2 * H + 2 ≤ ((Finset.Icc 1 Y).lcm id) / 1189 := by omega
    let L_int : ℤ := ((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ)
    let I_L := Finset.Icc (-L_int / 2) ((L_int + 1) / 2 - 1)
    have h_sub : Finset.Icc (-(H : ℤ)) (H : ℤ) ⊆ I_L := by
      intro a ha
      dsimp [I_L, L_int]
      rw [Finset.mem_Icc] at ha ⊢
      omega
    have h_term : ∀ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
        |φ (l_seq Y) a| ≤
          Real.exp (- (1 / 3 : ℝ) * ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * r i.1)) ^ 2) := by
      intro a _
      have h_p2 := (prefix_cosine_product_monotone_and_lipschitz r hr_nonneg (l_seq Y) (l_seq Y) le_rfl a 0).2.1
      have h_sum_eq : (∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * r i.1)) ^ 2) =
          ∑ k ∈ Finset.range (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * r k)) ^ 2 :=
        Fin.sum_univ_eq_sum_range (fun k => (Real.sin (Real.pi * (a : ℝ) * r k)) ^ 2) (l_seq Y)
      rwa [h_sum_eq]
    calc U Y H
        ≤ ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            Real.exp (- (1 / 3 : ℝ) * ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * r i.1)) ^ 2) :=
          Finset.sum_le_sum h_term
      _ ≤ ∑ a ∈ I_L,
            Real.exp (- (1 / 3 : ℝ) * ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * r i.1)) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
          intro a _ _
          exact le_of_lt (Real.exp_pos _)
      _ ≤ (C_m : ℝ) := h_kern Y hY_B
  obtain ⟨A₀, hA₀_ge1, h_stab⟩ :=
    monotone_antitone_tail_stabilization B (C_m : ℝ) S U hCm_r hS_props hU_Y_props hU_H_props hU_bound
  let D_denom : ℝ := (400 * (Nat.ceil C_m + 1) : ℝ)
  let δ : ℝ := 1 / D_denom
  let δ₀ : ℝ := Real.pi * δ
  have hδ_pos : 0 < δ := by
    dsimp [δ, D_denom]
    positivity
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    dsimp [δ, D_denom]
    have h_d : (4 : ℝ) ≤ (400 * (Nat.ceil C_m + 1) : ℝ) := by
      have : 4 ≤ 400 * (Nat.ceil C_m + 1) := by omega
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ₀_pos : 0 < δ₀ := mul_pos Real.pi_pos hδ_pos
  have hδ₀_lt_pi : δ₀ < Real.pi := by
    dsimp [δ₀]
    have h_lt1 : δ < 1 := lt_of_le_of_lt hδ_le_quarter (by norm_num)
    nlinarith [Real.pi_pos]
  have h_sin_pos : 0 < Real.sin δ₀ := Real.sin_pos_of_pos_of_lt_pi hδ₀_pos hδ₀_lt_pi
  let s₀ : ℝ := (Real.sin δ₀) ^ 2
  have hs₀_pos : 0 < s₀ := sq_pos_of_pos h_sin_pos
  obtain ⟨m_sin, hm_sin⟩ := exists_nat_gt (8 / s₀)
  obtain ⟨m_cm, hm_cm⟩ := exists_nat_gt ((A₀ : ℝ) * (C_m : ℝ))
  let m : ℕ := max A₀ (max m_sin m_cm)
  have hm_ge_A₀ : A₀ ≤ m := le_max_left _ _
  have hm_ge1 : 1 ≤ m := le_trans hA₀_ge1 hm_ge_A₀
  have hm_pos_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_ge1
  have hm_cm_le : (A₀ : ℝ) * (C_m : ℝ) ≤ (m : ℝ) := by
    have h1 : (m_cm : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have h_sin_bound : 1 / ((m : ℝ) * s₀) ≤ 1 / 8 := by
    have h1 : (m_sin : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : 8 < (m : ℝ) * s₀ := by
      have h3 : 8 < (m_sin : ℝ) * s₀ := (div_lt_iff₀ hs₀_pos).mp hm_sin
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨Y_star, hY_star_max, hU_star_diff, hS_star_diff, hU_low_all⟩ := h_stab m hm_ge_A₀
  have hY_star_B : B ≤ Y_star := le_trans (le_max_left _ _) hY_star_max
  let l_star := l_seq Y_star
  let r_star : Fin l_star → ℝ := fun i => r i.1
  have hr_star_sum : ∑ i : Fin l_star, r_star i ≤ 1 / 100 := by
    have h_eq : (∑ i : Fin l_star, r_star i) = S Y_star :=
      Fin.sum_univ_eq_sum_range r l_star
    rw [h_eq]
    exact (hS_props.1 Y_star).2
  have h_prod_abs_eq : ∀ (Y : ℕ) (a : ℤ),
      (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * r i.1)|) = |φ (l_seq Y) a| := by
    intro Y a
    rw [← Finset.abs_prod]
    congr 1
    exact Fin.prod_univ_eq_prod_range (fun k => Real.cos (Real.pi * (a : ℝ) * r k)) (l_seq Y)
  have h_kern_star : ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (∏ i : Fin l_star, |Real.cos (Real.pi * (a : ℝ) * r_star i)|) ≤ (C_m : ℝ) := by
    have h_eq : (∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (∏ i : Fin l_star, |Real.cos (Real.pi * (a : ℝ) * r_star i)|)) = U Y_star m := by
      apply Finset.sum_congr rfl
      intro a _
      exact h_prod_abs_eq Y_star a
    rw [h_eq]
    exact hU_bound m Y_star hY_star_max
  let F_m : ℝ → ℝ := fun u =>
    ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (1 - |(a : ℝ)| / (m : ℝ)) * Real.cos (2 * Real.pi * (a : ℝ) * u)
  let G_star : ℝ → ℝ := fun x =>
    ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (1 - |(a : ℝ)| / (m : ℝ)) *
        Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l_star, r_star i) - 2 * x)) *
        ∏ i : Fin l_star, Real.cos (Real.pi * (a : ℝ) * r_star i)
  have hG_rep : ∀ x : ℝ, G_star x =
      ((1 / 2 : ℝ) ^ l_star) *
        ∑ S_sub ∈ (Finset.univ : Finset (Fin l_star)).powerset,
          F_m ((∑ i ∈ S_sub, r_star i) - x) := by
    intro x
    dsimp [G_star, F_m]
    have h_term : ∀ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        (1 - |(a : ℝ)| / (m : ℝ)) *
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l_star, r_star i) - 2 * x)) *
          (∏ i : Fin l_star, Real.cos (Real.pi * (a : ℝ) * r_star i)) =
        ((1 / 2 : ℝ) ^ l_star) *
          ∑ S_sub ∈ (Finset.univ : Finset (Fin l_star)).powerset,
            (1 - |(a : ℝ)| / (m : ℝ)) * Real.cos (2 * Real.pi * (a : ℝ) * ((∑ i ∈ S_sub, r_star i) - x)) := by
      intro a _
      have h_id := reserve_subset_cosine_product_identity l_star r_star (- 2 * Real.pi * (a : ℝ) * x) a
      have h_arg_rhs : - 2 * Real.pi * (a : ℝ) * x + Real.pi * (a : ℝ) * ∑ i : Fin l_star, r_star i =
          Real.pi * (a : ℝ) * ((∑ i : Fin l_star, r_star i) - 2 * x) := by ring
      rw [h_arg_rhs] at h_id
      rw [mul_assoc, ← h_id, ← mul_assoc, mul_comm (1 - |(a : ℝ)| / (m : ℝ)) ((1 / 2 : ℝ) ^ l_star),
        mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro S_sub _
      congr 1
      congr 1
      ring
    rw [Finset.sum_congr rfl h_term, ← Finset.mul_sum, Finset.sum_comm]
  have hG_nonneg : ∀ x : ℝ, 0 ≤ G_star x := by
    intro x
    rw [hG_rep x]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro S_sub _
    exact (fejer_kernel_nonneg_and_exterior_bound m hm_ge1 ((∑ i ∈ S_sub, r_star i) - x)).1
  have hG_ext : ∀ x : ℝ, 1 / 100 + δ ≤ x → x ≤ 1 - δ → G_star x ≤ 1 / 8 := by
    intro x hx_low hx_high
    rw [hG_rep x]
    have h_sub_le : ∀ S_sub ∈ (Finset.univ : Finset (Fin l_star)).powerset,
        F_m ((∑ i ∈ S_sub, r_star i) - x) ≤ 1 / 8 := by
      intro S_sub _
      have h_sub_nonneg : 0 ≤ ∑ i ∈ S_sub, r_star i :=
        Finset.sum_nonneg (fun i _ => hr_nonneg i.1)
      have h_sub_top : ∑ i ∈ S_sub, r_star i ≤ 1 / 100 := by
        have h_le_all : ∑ i ∈ S_sub, r_star i ≤ ∑ i : Fin l_star, r_star i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S_sub) (fun i _ _ => hr_nonneg i.1)
        exact le_trans h_le_all hr_star_sum
      have h_u1 : δ ≤ - ((∑ i ∈ S_sub, r_star i) - x) := by linarith
      have h_u2 : - ((∑ i ∈ S_sub, r_star i) - x) ≤ 1 - δ := by linarith
      have h_fej := (fejer_kernel_nonneg_and_exterior_bound m hm_ge1 ((∑ i ∈ S_sub, r_star i) - x)).2
        δ hδ_pos hδ_le_quarter h_u1 h_u2
      exact le_trans h_fej h_sin_bound
    have h_card : ((Finset.univ : Finset (Fin l_star)).powerset.card : ℝ) = (2 : ℝ) ^ l_star := by
      simp
    calc ((1 / 2 : ℝ) ^ l_star) *
          ∑ S_sub ∈ (Finset.univ : Finset (Fin l_star)).powerset,
            F_m ((∑ i ∈ S_sub, r_star i) - x)
        ≤ ((1 / 2 : ℝ) ^ l_star) *
          ∑ _S_sub ∈ (Finset.univ : Finset (Fin l_star)).powerset, (1 / 8 : ℝ) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_sub_le) (by positivity)
      _ = ((1 / 2 : ℝ) ^ l_star) * ((2 : ℝ) ^ l_star * (1 / 8 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, h_card]
      _ = (((1 / 2 : ℝ) * 2) ^ l_star) * (1 / 8 : ℝ) := by
          rw [← mul_assoc, ← mul_pow]
      _ = 1 / 8 := by norm_num
  obtain ⟨x_d, hxd_pos, hxd_lt, hG_ge20⟩ :=
    rational_grid_fejer_peak_existence l_star m C_m r_star hm_ge1 hCm h_kern_star hG_nonneg hG_ext
  refine ⟨x_d, 16, A₀, hxd_pos, hxd_lt, by norm_num, hA₀_ge1, fun H₀ hH₀ => ?_⟩
  obtain ⟨Y_low, hY_low_star, hU_low⟩ := hU_low_all H₀ hH₀
  refine ⟨Y_low, le_trans hY_star_B hY_low_star, fun Y hY => ?_⟩
  have hY_ge_star : Y_star ≤ Y := le_trans hY_low_star hY
  have h_term_eq : ∀ (Y' : ℕ) (a : ℤ),
      Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin (l_seq Y'), r i.1) - 2 * (x_d : ℝ))) *
        (∏ i : Fin (l_seq Y'), Real.cos (Real.pi * (a : ℝ) * r i.1)) =
      τ (l_seq Y') a (x_d : ℝ) := by
    intro Y' a
    dsimp [τ]
    rw [Fin.sum_univ_eq_sum_range r (l_seq Y'),
      Fin.prod_univ_eq_prod_range (fun k => Real.cos (Real.pi * (a : ℝ) * r k)) (l_seq Y')]
  have h_tau_le_phi : ∀ (Y' : ℕ) (a : ℤ), |τ (l_seq Y') a (x_d : ℝ)| ≤ |φ (l_seq Y') a| := by
    intro Y' a
    dsimp [τ]
    rw [abs_mul]
    calc |Real.cos (Real.pi * (a : ℝ) * (σ (l_seq Y') - 2 * (x_d : ℝ)))| * |φ (l_seq Y') a|
        ≤ 1 * |φ (l_seq Y') a| :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |φ (l_seq Y') a| := one_mul _
  let I_A₀ := Finset.Icc (-(A₀ : ℤ)) (A₀ : ℤ)
  let I_m := Finset.Icc (-(m : ℤ)) (m : ℤ)
  let I_H₀ := Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ)
  have h_sub_A₀_m : I_A₀ ⊆ I_m := by
    intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    omega
  have h_sub_A₀_H₀ : I_A₀ ⊆ I_H₀ := by
    intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    omega
  have hG_star : 20 ≤ ∑ a ∈ I_m, (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ) := by
    have h_eq : (∑ a ∈ I_m, (1 - |(a : ℝ)| / (m : ℝ)) *
        Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l_star, r_star i) - 2 * (x_d : ℝ))) *
        ∏ i : Fin l_star, Real.cos (Real.pi * (a : ℝ) * r_star i)) =
        ∑ a ∈ I_m, (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, h_term_eq Y_star a]
    rwa [← h_eq]
  have h_G_split : (∑ a ∈ I_m, (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) =
      (∑ a ∈ I_A₀, τ l_star a (x_d : ℝ)) -
      (∑ a ∈ I_A₀, (|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) +
      (∑ a ∈ I_m \ I_A₀, (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) := by
    rw [← Finset.sum_sdiff h_sub_A₀_m]
    have h_low_eq : (∑ a ∈ I_A₀, (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) =
        (∑ a ∈ I_A₀, τ l_star a (x_d : ℝ)) -
        (∑ a ∈ I_A₀, (|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [h_low_eq]
    ring
  have h_err1 : - (∑ a ∈ I_A₀, (|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) ≤ 1 := by
    have h_term_le : ∀ a ∈ I_A₀,
        - ((|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) ≤ ((A₀ : ℝ) / (m : ℝ)) * |φ l_star a| := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha_abs : |(a : ℝ)| ≤ (A₀ : ℝ) := by
        rw [abs_le]
        constructor <;> exact_mod_cast (by omega)
      have h_div_le : |(a : ℝ)| / (m : ℝ) ≤ (A₀ : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_right ha_abs (le_of_lt hm_pos_r)
      have hw_nonneg : 0 ≤ |(a : ℝ)| / (m : ℝ) := div_nonneg (abs_nonneg _) (le_of_lt hm_pos_r)
      have h_neg : - τ l_star a (x_d : ℝ) ≤ |τ l_star a (x_d : ℝ)| := neg_le_abs _
      have h1 : - ((|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) ≤
          (|(a : ℝ)| / (m : ℝ)) * |τ l_star a (x_d : ℝ)| := by
        calc - ((|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ))
            = (|(a : ℝ)| / (m : ℝ)) * (- τ l_star a (x_d : ℝ)) := by ring
          _ ≤ (|(a : ℝ)| / (m : ℝ)) * |τ l_star a (x_d : ℝ)| :=
              mul_le_mul_of_nonneg_left h_neg hw_nonneg
      calc - ((|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ))
          ≤ (|(a : ℝ)| / (m : ℝ)) * |τ l_star a (x_d : ℝ)| := h1
        _ ≤ ((A₀ : ℝ) / (m : ℝ)) * |φ l_star a| :=
            mul_le_mul h_div_le (h_tau_le_phi Y_star a) (abs_nonneg _) (by positivity)
    rw [← Finset.sum_neg_distrib]
    calc ∑ a ∈ I_A₀, - ((|(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ))
        ≤ ∑ a ∈ I_A₀, ((A₀ : ℝ) / (m : ℝ)) * |φ l_star a| := Finset.sum_le_sum h_term_le
      _ = ((A₀ : ℝ) / (m : ℝ)) * U Y_star A₀ := (Finset.mul_sum _ _ _).symm
      _ ≤ ((A₀ : ℝ) / (m : ℝ)) * (C_m : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_trans (hU_H_props Y_star A₀ m hm_ge_A₀) (hU_bound m Y_star hY_star_max)
      _ = ((A₀ : ℝ) * (C_m : ℝ)) / (m : ℝ) := div_mul_eq_mul_div _ _ _
      _ ≤ 1 := (div_le_one hm_pos_r).mpr hm_cm_le
  have h_err2 : (∑ a ∈ I_m \ I_A₀, (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)) ≤ 2 := by
    have h_term_le : ∀ a ∈ I_m \ I_A₀,
        (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ) ≤ |φ l_star a| := by
      intro a ha
      have ha_m : a ∈ I_m := (Finset.mem_sdiff.mp ha).1
      rw [Finset.mem_Icc] at ha_m
      have ha_abs : |(a : ℝ)| ≤ (m : ℝ) := by
        rw [abs_le]
        constructor <;> exact_mod_cast (by omega)
      have hw_nonneg : 0 ≤ 1 - |(a : ℝ)| / (m : ℝ) := by
        have : |(a : ℝ)| / (m : ℝ) ≤ 1 := (div_le_one hm_pos_r).mpr ha_abs
        linarith
      have hw_le1 : 1 - |(a : ℝ)| / (m : ℝ) ≤ 1 := by
        have : 0 ≤ |(a : ℝ)| / (m : ℝ) := by positivity
        linarith
      calc (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)
          ≤ (1 - |(a : ℝ)| / (m : ℝ)) * |τ l_star a (x_d : ℝ)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hw_nonneg
        _ ≤ 1 * |φ l_star a| :=
            mul_le_mul hw_le1 (h_tau_le_phi Y_star a) (abs_nonneg _) zero_le_one
        _ = |φ l_star a| := one_mul _
    have h_sdiff_U : (∑ a ∈ I_m \ I_A₀, |φ l_star a|) = U Y_star m - U Y_star A₀ := by
      have h_u := Finset.sum_sdiff h_sub_A₀_m (f := fun a => |φ l_star a|)
      linarith
    calc ∑ a ∈ I_m \ I_A₀, (1 - |(a : ℝ)| / (m : ℝ)) * τ l_star a (x_d : ℝ)
        ≤ ∑ a ∈ I_m \ I_A₀, |φ l_star a| := Finset.sum_le_sum h_term_le
      _ = U Y_star m - U Y_star A₀ := h_sdiff_U
      _ ≤ 2 := hU_star_diff
  have hD_star : 17 ≤ ∑ a ∈ I_A₀, τ l_star a (x_d : ℝ) := by linarith
  have h_drift : (∑ a ∈ I_A₀, τ l_star a (x_d : ℝ)) - (∑ a ∈ I_A₀, τ (l_seq Y) a (x_d : ℝ)) ≤ 1 := by
    rw [← Finset.sum_sub_distrib]
    have h_term_drift : ∀ a ∈ I_A₀,
        τ l_star a (x_d : ℝ) - τ (l_seq Y) a (x_d : ℝ) ≤ 4 * (A₀ : ℝ) * (S Y - S Y_star) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha_abs : |(a : ℝ)| ≤ (A₀ : ℝ) := by
        rw [abs_le]
        constructor <;> exact_mod_cast (by omega)
      have h_lip := (prefix_cosine_product_monotone_and_lipschitz r hr_nonneg
        l_star (l_seq Y) (h_mono.2 Y_star Y hY_ge_star) a (x_d : ℝ)).2.2
      have h_diff_nonneg : 0 ≤ S Y - S Y_star := sub_nonneg.mpr (hS_props.2 Y_star Y hY_ge_star)
      have h_abs : τ l_star a (x_d : ℝ) - τ (l_seq Y) a (x_d : ℝ) ≤
          |τ (l_seq Y) a (x_d : ℝ) - τ l_star a (x_d : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      calc τ l_star a (x_d : ℝ) - τ (l_seq Y) a (x_d : ℝ)
          ≤ |τ (l_seq Y) a (x_d : ℝ) - τ l_star a (x_d : ℝ)| := h_abs
        _ ≤ 4 * |(a : ℝ)| * (S Y - S Y_star) := h_lip
        _ ≤ 4 * (A₀ : ℝ) * (S Y - S Y_star) := by
            nlinarith
    have h_card : (I_A₀.card : ℝ) = 2 * (A₀ : ℝ) + 1 := by
      dsimp [I_A₀]
      rw [Int.card_Icc]
      have h_int : (A₀ : ℤ) + 1 - -(A₀ : ℤ) = ((2 * A₀ + 1 : ℕ) : ℤ) := by omega
      rw [h_int, Int.toNat_natCast]
      push_cast
      ring
    calc ∑ a ∈ I_A₀, (τ l_star a (x_d : ℝ) - τ (l_seq Y) a (x_d : ℝ))
        ≤ ∑ a ∈ I_A₀, 4 * (A₀ : ℝ) * (S Y - S Y_star) := Finset.sum_le_sum h_term_drift
      _ = (I_A₀.card : ℝ) * (4 * (A₀ : ℝ) * (S Y - S Y_star)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (4 * (2 * (A₀ : ℝ) + 1) * (A₀ : ℝ)) * (S Y - S Y_star) := by
          rw [h_card]; ring
      _ ≤ (4 * (2 * (A₀ : ℝ) + 1) * (A₀ : ℝ)) * (1 / (4 * (2 * (A₀ : ℝ) + 1) * (A₀ : ℝ))) := by
          apply mul_le_mul_of_nonneg_left (hS_star_diff Y hY_ge_star)
          have : (1 : ℝ) ≤ (A₀ : ℝ) := by exact_mod_cast hA₀_ge1
          positivity
      _ = 1 := by
          have h_pos : (0 : ℝ) < 4 * (2 * (A₀ : ℝ) + 1) * (A₀ : ℝ) := by
            have : (1 : ℝ) ≤ (A₀ : ℝ) := by exact_mod_cast hA₀_ge1
            positivity
          exact mul_one_div_cancel (ne_of_gt h_pos)
  have hD_Y_A₀ : 16 ≤ ∑ a ∈ I_A₀, τ (l_seq Y) a (x_d : ℝ) := by linarith
  have h_tail_H₀ : - (∑ a ∈ I_H₀ \ I_A₀, τ (l_seq Y) a (x_d : ℝ)) ≤ 2 := by
    rw [← Finset.sum_neg_distrib]
    have h_term_le : ∀ a ∈ I_H₀ \ I_A₀, - τ (l_seq Y) a (x_d : ℝ) ≤ |φ (l_seq Y) a| := by
      intro a _
      exact le_trans (neg_le_abs _) (h_tau_le_phi Y a)
    have h_sdiff_U : (∑ a ∈ I_H₀ \ I_A₀, |φ (l_seq Y) a|) = U Y H₀ - U Y A₀ := by
      have h_u := Finset.sum_sdiff h_sub_A₀_H₀ (f := fun a => |φ (l_seq Y) a|)
      linarith
    calc ∑ a ∈ I_H₀ \ I_A₀, - τ (l_seq Y) a (x_d : ℝ)
        ≤ ∑ a ∈ I_H₀ \ I_A₀, |φ (l_seq Y) a| := Finset.sum_le_sum h_term_le
      _ = U Y H₀ - U Y A₀ := h_sdiff_U
      _ ≤ 2 := hU_low Y hY
  have h_split_H₀ : (∑ a ∈ I_H₀, τ (l_seq Y) a (x_d : ℝ)) =
      (∑ a ∈ I_A₀, τ (l_seq Y) a (x_d : ℝ)) + (∑ a ∈ I_H₀ \ I_A₀, τ (l_seq Y) a (x_d : ℝ)) := by
    linarith [Finset.sum_sdiff h_sub_A₀_H₀ (f := fun a => τ (l_seq Y) a (x_d : ℝ))]
  have h_goal_eq : (∑ a ∈ I_H₀,
      Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin (l_seq Y), r i.1) - 2 * (x_d : ℝ))) *
        ∏ i : Fin (l_seq Y), Real.cos (Real.pi * (a : ℝ) * r i.1)) =
      ∑ a ∈ I_H₀, τ (l_seq Y) a (x_d : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    exact h_term_eq Y a
  change 3 / 4 * ((16 : ℚ) : ℝ) ≤
    ∑ a ∈ I_H₀,
      Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin (l_seq Y), r i.1) - 2 * (x_d : ℝ))) *
        ∏ i : Fin (l_seq Y), Real.cos (Real.pi * (a : ℝ) * r i.1)
  rw [h_goal_eq, h_split_H₀]
  push_cast
  linarith

theorem coherent_reserve_fourier_profile_existence : ∃ (Y₀ H₀ : ℕ) (l_seq : ℕ → ℕ) (R_seq : ∀ Y : ℕ, Fin (l_seq Y) → ℕ × ℕ) (x_d g₀ : ℚ),
      1189 ≤ Y₀ ∧ 1 ≤ H₀ ∧ 0 < x_d ∧ x_d < 1 / 100 ∧ 0 < g₀ ∧
      ∀ Y ≥ Y₀,
        (∀ i : Fin (l_seq Y), 495 ≤ (R_seq Y i).1 ∧ (R_seq Y i).1 < (R_seq Y i).2 ∧ (R_seq Y i).2 ≤ (R_seq Y i).1 + 2) ∧
        (∀ i j : Fin (l_seq Y), i ≠ j → (R_seq Y i).2 + 1 < (R_seq Y j).1 ∨ (R_seq Y j).2 + 1 < (R_seq Y i).1) ∧
        (∑ i : Fin (l_seq Y), w_Icc (R_seq Y i).1 (R_seq Y i).2 ≤ 1 / 118900) ∧
        (∀ N : ℕ, Y ^ 512 ≤ N ^ 511 → 537800 * (l_seq Y + 4) ≤ N) ∧
        (∀ i : Fin (l_seq Y), ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (R_seq Y i).1 (R_seq Y i).2).den = 1) ∧
        (3 / 4 * (g₀ : ℝ) ≤
          ∑ a ∈ Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ),
            Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin (l_seq Y), (1189 * (w_Icc (R_seq Y i).1 (R_seq Y i).2 : ℝ))) - 2 * (x_d : ℝ))) *
              ∏ i : Fin (l_seq Y), Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (R_seq Y i).1 (R_seq Y i).2 : ℝ)))) ∧
        (∑ a ∈ (Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2) ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1)) \
            (Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ)),
            (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (R_seq Y i).1 (R_seq Y i).2 : ℝ)))|) ≤
          1 / 4 * (g₀ : ℝ)) :=
by
  classical
  obtain ⟨B, C_m, l_seq, I_seq, hB, hCm, h_bounds, h_sep, h_mono, h_mass, h_scale_lcm, h_kern, h_conf⟩ :=
    nested_reserve_with_sine_energy_existence
  obtain ⟨x_d, g₀, A₀, hxd_pos, hxd_lt, hg₀_pos, hA₀_ge1, h_low_all⟩ :=
    fejer_limit_density_and_low_freq_positivity B C_m l_seq I_seq hB hCm h_mono h_bounds h_mass h_kern
  let M : ℝ := max 1 (6 * Real.log (4 * (C_m : ℝ) / (g₀ : ℝ)))
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨C_M, Y_M, hYM_B, hCM_ge1, h_conf_M⟩ := h_conf M hM_pos
  let H₀ : ℕ := max A₀ C_M
  obtain ⟨Y_low, hYlow_B, h_low_H₀⟩ := h_low_all H₀ (le_max_left A₀ C_M)
  let Y₀ : ℕ := max B (max (2 ^ 100000) (max Y_M Y_low))
  let R_seq : ∀ Y : ℕ, Fin (l_seq Y) → ℕ × ℕ := fun Y i => I_seq i.1
  have hB_le_Y₀ : B ≤ Y₀ := le_max_left _ _
  have h2_le_Y₀ : 2 ^ 100000 ≤ Y₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hYM_le_Y₀ : Y_M ≤ Y₀ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hYlow_le_Y₀ : Y_low ≤ Y₀ := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨Y₀, H₀, l_seq, R_seq, x_d, g₀, le_trans hB hB_le_Y₀, le_trans hA₀_ge1 (le_max_left _ _),
    hxd_pos, hxd_lt, hg₀_pos, fun Y hY => ?_⟩
  have hY_B : B ≤ Y := le_trans hB_le_Y₀ hY
  have hY_2 : 2 ^ 100000 ≤ Y := le_trans h2_le_Y₀ hY
  have hY_YM : Y_M ≤ Y := le_trans hYM_le_Y₀ hY
  have hY_Ylow : Y_low ≤ Y := le_trans hYlow_le_Y₀ hY
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro i
    exact h_bounds i.1
  · 
    intro i j hij
    apply h_sep
    intro h_eq
    exact hij (Fin.ext h_eq)
  · 
    change ∑ i : Fin (l_seq Y), w_Icc (I_seq i.1).1 (I_seq i.1).2 ≤ 1 / 118900
    rw [Fin.sum_univ_eq_sum_range (fun k => w_Icc (I_seq k).1 (I_seq k).2) (l_seq Y)]
    exact h_mass (l_seq Y)
  · 
    intro N hYN
    have hl₀ : l_seq Y ≤ 2 ^ 57 * Y * (Nat.log 2 Y + 1) ^ 3 := (h_scale_lcm Y hY_B).1
    have hY_pos : 0 < Y := lt_of_lt_of_le (Nat.two_pow_pos 100000) hY_2
    set K := Nat.log 2 Y
    have hK_ge : 100000 ≤ K := by
      have h1 : Nat.log 2 (2 ^ 100000) ≤ Nat.log 2 Y := Nat.log_mono_right hY_2
      rwa [Nat.log_pow (by decide : 1 < 2)] at h1
    have h2K_le : 2 ^ K ≤ Y := Nat.pow_log_le_self 2 (by omega)
    set x := K / 4096
    have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
    have hK1_le : K + 1 ≤ 2 ^ (12 + x) := by
      have h_div : K + 1 ≤ 2 ^ 12 * (x + 1) := by omega
      have h_pow : 2 ^ 12 * (x + 1) ≤ 2 ^ 12 * 2 ^ x :=
        Nat.mul_le_mul_left (2 ^ 12) (by omega)
      rw [← Nat.pow_add] at h_pow
      exact le_trans h_div h_pow
    have hK1_cube : (K + 1) ^ 3 ≤ 2 ^ (36 + 3 * x) := by
      calc (K + 1) ^ 3 ≤ (2 ^ (12 + x)) ^ 3 := Nat.pow_le_pow_left hK1_le 3
        _ = 2 ^ ((12 + x) * 3) := (Nat.pow_mul 2 (12 + x) 3).symm
        _ = 2 ^ (36 + 3 * x) := by ring_nf
    have h_prod_pos : 1 ≤ Y * (K + 1) ^ 3 := Nat.mul_pos hY_pos (by positivity)
    have hl₀_plus4 : l_seq Y + 4 ≤ 2 ^ 58 * Y * (K + 1) ^ 3 := by
      have h4 : 4 ≤ 2 ^ 57 * (Y * (K + 1) ^ 3) := by omega
      linarith
    have h_lhs : 537800 * (l_seq Y + 4) ≤ 2 ^ (114 + 3 * x) * Y := by
      have h537 : 537800 ≤ 2 ^ 20 := by norm_num
      calc 537800 * (l_seq Y + 4) ≤ 2 ^ 20 * (2 ^ 58 * Y * (K + 1) ^ 3) :=
            Nat.mul_le_mul h537 hl₀_plus4
        _ = 2 ^ 78 * (K + 1) ^ 3 * Y := by ring
        _ ≤ 2 ^ 78 * 2 ^ (36 + 3 * x) * Y := by
            apply Nat.mul_le_mul_right Y
            exact Nat.mul_le_mul_left (2 ^ 78) hK1_cube
        _ = 2 ^ (114 + 3 * x) * Y := by
            rw [← Nat.pow_add]
            ring_nf
    have h_exp_le : 511 * (114 + 3 * x) ≤ K := by omega
    have h_pow2_le : 2 ^ (511 * (114 + 3 * x)) ≤ Y :=
      le_trans (Nat.pow_le_pow_right (by decide) h_exp_le) h2K_le
    have h_pow511 : (537800 * (l_seq Y + 4)) ^ 511 ≤ N ^ 511 := by
      calc (537800 * (l_seq Y + 4)) ^ 511 ≤ (2 ^ (114 + 3 * x) * Y) ^ 511 :=
            Nat.pow_le_pow_left h_lhs 511
        _ = (2 ^ (114 + 3 * x)) ^ 511 * Y ^ 511 := Nat.mul_pow _ _ 511
        _ = 2 ^ (511 * (114 + 3 * x)) * Y ^ 511 := by
            rw [← Nat.pow_mul]
            ring
        _ ≤ Y * Y ^ 511 := Nat.mul_le_mul_right (Y ^ 511) h_pow2_le
        _ = Y ^ 512 := by ring
        _ ≤ N ^ 511 := hYN
    exact (Nat.pow_le_pow_iff_left (by decide : 511 ≠ 0)).mp h_pow511
  · 
    exact (h_scale_lcm Y hY_B).2
  · 
    exact h_low_H₀ Y hY_Ylow
  · 
    let I_L := Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2)
      ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1)
    let I_H := Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ)
    let E : ℤ → ℝ := fun a =>
      ∑ i : Fin (l_seq Y), (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2
    have hCm_pos : (0 : ℝ) < (C_m : ℝ) := Rat.cast_pos.mpr hCm
    have hg₀_pos_r : (0 : ℝ) < (g₀ : ℝ) := Rat.cast_pos.mpr hg₀_pos
    have h_cos_exp : ∀ x : ℝ, |Real.cos x| ≤ Real.exp (- (1 / 2 : ℝ) * (Real.sin x) ^ 2) := by
      intro x
      have h1 : (Real.cos x) ^ 2 ≤ Real.exp (- (Real.sin x) ^ 2) := by
        have h_id := Real.sin_sq_add_cos_sq x
        have h_exp := Real.add_one_le_exp (- (Real.sin x) ^ 2)
        linarith
      have h2 : |Real.cos x| ^ 2 ≤ (Real.exp (- (1 / 2 : ℝ) * (Real.sin x) ^ 2)) ^ 2 := by
        rw [sq_abs, sq (Real.exp _), ← Real.exp_add]
        have h_eq : - (1 / 2 : ℝ) * (Real.sin x) ^ 2 + - (1 / 2 : ℝ) * (Real.sin x) ^ 2 = - (Real.sin x) ^ 2 := by ring
        rw [h_eq]
        exact h1
      have h3 : 0 ≤ |Real.cos x| := abs_nonneg _
      have h4 : 0 < Real.exp (- (1 / 2 : ℝ) * (Real.sin x) ^ 2) := Real.exp_pos _
      nlinarith
    have h_term : ∀ a ∈ I_L \ I_H,
        (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))|) ≤
          (g₀ : ℝ) / (4 * (C_m : ℝ)) * Real.exp (- (1 / 3 : ℝ) * E a) := by
      intro a ha
      have ha_CM : a ∈ I_L \ Finset.Icc (-(C_M : ℤ)) (C_M : ℤ) := by
        simp only [I_H, Finset.mem_sdiff, Finset.mem_Icc] at ha ⊢
        have hCM_H₀ : (C_M : ℤ) ≤ (H₀ : ℤ) := by exact_mod_cast le_max_right A₀ C_M
        exact ⟨ha.1, by omega⟩
      have hEa_ge_M : M ≤ E a := h_conf_M Y hY_YM a ha_CM
      have hEa_ge : 6 * Real.log (4 * (C_m : ℝ) / (g₀ : ℝ)) ≤ E a :=
        le_trans (le_max_right _ _) hEa_ge_M
      have h_prod : (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))|) ≤
          Real.exp (- (1 / 2 : ℝ) * E a) := by
        calc (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))|)
            ≤ ∏ i : Fin (l_seq Y), Real.exp (- (1 / 2 : ℝ) * (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2) := by
              apply Finset.prod_le_prod
              · intro i _; exact abs_nonneg _
              · intro i _; exact h_cos_exp _
          _ = Real.exp (∑ i : Fin (l_seq Y), - (1 / 2 : ℝ) * (Real.sin (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))) ^ 2) :=
              (Real.exp_sum _ _).symm
          _ = Real.exp (- (1 / 2 : ℝ) * E a) := by
              rw [← Finset.mul_sum]
      have h_split : Real.exp (- (1 / 2 : ℝ) * E a) = Real.exp (- (1 / 6 : ℝ) * E a) * Real.exp (- (1 / 3 : ℝ) * E a) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h_exp_six : Real.exp (- (1 / 6 : ℝ) * E a) ≤ (g₀ : ℝ) / (4 * (C_m : ℝ)) := by
        have h_le_log : - (1 / 6 : ℝ) * E a ≤ - Real.log (4 * (C_m : ℝ) / (g₀ : ℝ)) := by linarith
        calc Real.exp (- (1 / 6 : ℝ) * E a)
            ≤ Real.exp (- Real.log (4 * (C_m : ℝ) / (g₀ : ℝ))) := Real.exp_le_exp.mpr h_le_log
          _ = (Real.exp (Real.log (4 * (C_m : ℝ) / (g₀ : ℝ))))⁻¹ := Real.exp_neg _
          _ = (4 * (C_m : ℝ) / (g₀ : ℝ))⁻¹ := by
              rw [Real.exp_log (by positivity)]
          _ = (g₀ : ℝ) / (4 * (C_m : ℝ)) := inv_div _ _
      calc (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))|)
          ≤ Real.exp (- (1 / 2 : ℝ) * E a) := h_prod
        _ = Real.exp (- (1 / 6 : ℝ) * E a) * Real.exp (- (1 / 3 : ℝ) * E a) := h_split
        _ ≤ (g₀ : ℝ) / (4 * (C_m : ℝ)) * Real.exp (- (1 / 3 : ℝ) * E a) :=
            mul_le_mul_of_nonneg_right h_exp_six (le_of_lt (Real.exp_pos _))
    have h_sum1 : ∑ a ∈ I_L \ I_H,
        (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))|) ≤
          (g₀ : ℝ) / (4 * (C_m : ℝ)) * ∑ a ∈ I_L \ I_H, Real.exp (- (1 / 3 : ℝ) * E a) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum h_term
    have h_sum2 : ∑ a ∈ I_L \ I_H, Real.exp (- (1 / 3 : ℝ) * E a) ≤ (C_m : ℝ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_) (h_kern Y hY_B)
      intro a _ _
      exact le_of_lt (Real.exp_pos _)
    calc ∑ a ∈ I_L \ I_H,
          (∏ i : Fin (l_seq Y), |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (I_seq i.1).1 (I_seq i.1).2 : ℝ)))|)
        ≤ (g₀ : ℝ) / (4 * (C_m : ℝ)) * ∑ a ∈ I_L \ I_H, Real.exp (- (1 / 3 : ℝ) * E a) := h_sum1
      _ ≤ (g₀ : ℝ) / (4 * (C_m : ℝ)) * (C_m : ℝ) :=
          mul_le_mul_of_nonneg_left h_sum2 (by positivity)
      _ = 1 / 4 * (g₀ : ℝ) := by
          field_simp [ne_of_gt hCm_pos]

theorem finite_fourier_subset_sum_extraction (H₀ : ℕ) (x_d g₀ : ℚ)
    (hH₀ : 1 ≤ H₀) (hxd_pos : 0 < x_d) (hxd_lt : x_d < 1 / 100) (hg₀_pos : 0 < g₀) :
    ∃ N_four : ℕ, 475600 ≤ N_four ∧ ∀ N ≥ N_four, ∀ Y ≥ 1189,
      Y ^ 512 ≤ N ^ 511 →
      ∀ (l₀ : ℕ) (R₀ : Fin l₀ → ℕ × ℕ),
        (∑ i : Fin l₀, w_Icc (R₀ i).1 (R₀ i).2 ≤ 1 / 118900) →
        (∀ i : Fin l₀, ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_Icc (R₀ i).1 (R₀ i).2).den = 1) →
        (3 / 4 * (g₀ : ℝ) ≤
          ∑ a ∈ Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ),
            Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, (1189 * (w_Icc (R₀ i).1 (R₀ i).2 : ℝ))) - 2 * (x_d : ℝ))) *
              ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (R₀ i).1 (R₀ i).2 : ℝ)))) →
        (∑ a ∈ (Finset.Icc (-((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) / 2) ((((((Finset.Icc 1 Y).lcm id) / 1189 : ℕ) : ℤ) + 1) / 2 - 1)) \
            (Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ)),
            (∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * (1189 * (w_Icc (R₀ i).1 (R₀ i).2 : ℝ)))|) ≤
          1 / 4 * (g₀ : ℝ)) →
        ∀ P : Finset ℕ,
          (∀ t ∈ P, ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_pkt t).den = 1) →
          N / 4800 ≤ P.card →
          (∀ t ∈ P, w_pkt t ≤ 6000 / (1189 * (N : ℚ))) →
          3 / 2 - 1 / 10 ≤ 1189 * ∑ t ∈ P, w_pkt t →
          1189 * ∑ t ∈ P, w_pkt t ≤ 3 / 2 + 1 / 10 →
          ∃ (T : Finset ℕ) (S : Finset (Fin l₀)),
            T ⊆ P ∧ ∑ t ∈ T, w_pkt t + ∑ i ∈ S, w_Icc (R₀ i).1 (R₀ i).2 = 1 / 1189 :=
by
  have rat_eq_num_of_den_eq_one : ∀ (q : ℚ), q.den = 1 → q = (q.num : ℚ) := by
    intro q h
    have := Rat.num_div_den q
    rw [h, Nat.cast_one, div_one] at this
    exact this.symm

  have h_greedy : ∀ (P : Finset ℕ) (δ τ : ℚ), (∀ t ∈ P, w_pkt t ≤ δ) →
      0 < δ → 0 ≤ τ → τ ≤ ∑ t ∈ P, w_pkt t →
      ∃ T : Finset ℕ, T ⊆ P ∧ τ - δ ≤ ∑ t ∈ T, w_pkt t ∧ ∑ t ∈ T, w_pkt t ≤ τ := by
    intro P δ τ hw_max hδ hτ_nonneg hτ_le
    induction P using Finset.induction_on with
    | empty =>
      refine ⟨∅, Finset.Subset.refl ∅, ?_, ?_⟩
      · simp only [Finset.sum_empty] at hτ_le ⊢
        linarith
      · simp only [Finset.sum_empty] at hτ_le ⊢
        linarith
    | @insert t₀ s ht₀ ih =>
      rw [Finset.sum_insert ht₀] at hτ_le
      by_cases h_sub : τ ≤ ∑ t ∈ s, w_pkt t
      · obtain ⟨T, hT_sub, hT_low, hT_high⟩ := ih
          (fun t ht => hw_max t (Finset.mem_insert_of_mem ht))
          h_sub
        exact ⟨T, Finset.Subset.trans hT_sub (Finset.subset_insert t₀ s), hT_low, hT_high⟩
      · refine ⟨s, Finset.subset_insert t₀ s, ?_, ?_⟩
        · have hw_t₀ : w_pkt t₀ ≤ δ := hw_max t₀ (Finset.mem_insert_self t₀ s)
          linarith
        · linarith

  have w_Icc_two : ∀ (a : ℕ), w_Icc a (a + 1) = (a : ℚ)⁻¹ + ((a + 1 : ℕ) : ℚ)⁻¹ := by
    intro a
    unfold w_Icc
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ a + 1), Finset.Icc_self, Finset.sum_singleton]

  have w_Icc_five : ∀ (a : ℕ), w_Icc a (a + 4) =
      (a : ℚ)⁻¹ + ((a + 1 : ℕ) : ℚ)⁻¹ + ((a + 2 : ℕ) : ℚ)⁻¹ +
        ((a + 3 : ℕ) : ℚ)⁻¹ + ((a + 4 : ℕ) : ℚ)⁻¹ := by
    intro a
    unfold w_Icc
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ a + 4)]
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ a + 3)]
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ a + 2)]
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ a + 1), Finset.Icc_self, Finset.sum_singleton]

  have h_elim : ∀ (t : ℕ), 2 ≤ t → ∃ (M A Q : ℤ),
      M = (6 * (t : ℤ) + 1) * Q + 25200 ∧
      ((M : ℚ) * (w_pkt t - ((6 * t + 1 : ℕ) : ℚ)⁻¹) = (A : ℚ)) := by
    intro t ht
    set u : ℤ := 6 * (t : ℤ) + 1
    have hu : (13 : ℚ) ≤ (u : ℚ) := by
      have : (13 : ℤ) ≤ u := by unfold u; omega
      exact_mod_cast this
    set M : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 3) * (u - 2) * (u - 1) *
      (u + 1) * (u + 2) * (u + 3) * (u + 5)
    let Q : ℤ := u^9 - 11*u^8 - 11*u^7 + 429*u^6 - 693*u^5 - 4389*u^4 + 9911*u^3 + 13871*u^2 - 34408*u - 9900
    have hQ : M = u * Q + 25200 := by unfold M Q; ring
    have h1 : w_Icc (2 * t - 2) (2 * t - 1) =
        ((2 * t - 2 : ℕ) : ℚ)⁻¹ + ((2 * t - 1 : ℕ) : ℚ)⁻¹ := by
      have := w_Icc_two (2 * t - 2)
      have heq : 2 * t - 2 + 1 = 2 * t - 1 := by omega
      rw [heq] at this; exact this
    have h2 : w_Icc (2 * t + 1) (2 * t + 2) =
        ((2 * t + 1 : ℕ) : ℚ)⁻¹ + ((2 * t + 2 : ℕ) : ℚ)⁻¹ := by
      have := w_Icc_two (2 * t + 1)
      have heq : 2 * t + 1 + 1 = 2 * t + 2 := by omega
      rw [heq] at this; exact this
    have h3 : w_Icc (3 * t - 2) (3 * t + 2) =
        ((3 * t - 2 : ℕ) : ℚ)⁻¹ + ((3 * t - 1 : ℕ) : ℚ)⁻¹ + ((3 * t : ℕ) : ℚ)⁻¹ +
        ((3 * t + 1 : ℕ) : ℚ)⁻¹ + ((3 * t + 2 : ℕ) : ℚ)⁻¹ := by
      have := w_Icc_five (3 * t - 2)
      have e1 : 3 * t - 2 + 1 = 3 * t - 1 := by omega
      have e2 : 3 * t - 2 + 2 = 3 * t := by omega
      have e3 : 3 * t - 2 + 3 = 3 * t + 1 := by omega
      have e4 : 3 * t - 2 + 4 = 3 * t + 2 := by omega
      rw [e1, e2, e3, e4] at this; exact this
    have h4 : w_Icc (6 * t - 2) (6 * t + 2) =
        ((6 * t - 2 : ℕ) : ℚ)⁻¹ + ((6 * t - 1 : ℕ) : ℚ)⁻¹ + ((6 * t : ℕ) : ℚ)⁻¹ +
        ((6 * t + 1 : ℕ) : ℚ)⁻¹ + ((6 * t + 2 : ℕ) : ℚ)⁻¹ := by
      have := w_Icc_five (6 * t - 2)
      have e1 : 6 * t - 2 + 1 = 6 * t - 1 := by omega
      have e2 : 6 * t - 2 + 2 = 6 * t := by omega
      have e3 : 6 * t - 2 + 3 = 6 * t + 1 := by omega
      have e4 : 6 * t - 2 + 4 = 6 * t + 2 := by omega
      rw [e1, e2, e3, e4] at this; exact this
    have h_wpkt : w_pkt t - ((6 * t + 1 : ℕ) : ℚ)⁻¹ =
        3 / ((u : ℚ) - 7) + 2 / ((u : ℚ) - 5) + 3 / ((u : ℚ) - 4) + 3 / ((u : ℚ) - 3) +
        1 / ((u : ℚ) - 2) + 3 / ((u : ℚ) - 1) + 3 / ((u : ℚ) + 1) + 3 / ((u : ℚ) + 2) +
        2 / ((u : ℚ) + 3) + 3 / ((u : ℚ) + 5) := by
      unfold w_pkt
      rw [h1, h2, h3, h4]
      have c1 : ((2 * t - 2 : ℕ) : ℚ) = ((u : ℚ) - 7) / 3 := by unfold u; push_cast [Nat.cast_sub (by omega : 2 ≤ 2 * t)]; ring
      have c2 : ((2 * t - 1 : ℕ) : ℚ) = ((u : ℚ) - 4) / 3 := by unfold u; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * t)]; ring
      have c3 : ((2 * t + 1 : ℕ) : ℚ) = ((u : ℚ) + 2) / 3 := by unfold u; push_cast; ring
      have c4 : ((2 * t + 2 : ℕ) : ℚ) = ((u : ℚ) + 5) / 3 := by unfold u; push_cast; ring
      have c5 : ((3 * t - 2 : ℕ) : ℚ) = ((u : ℚ) - 5) / 2 := by unfold u; push_cast [Nat.cast_sub (by omega : 2 ≤ 3 * t)]; ring
      have c6 : ((3 * t - 1 : ℕ) : ℚ) = ((u : ℚ) - 3) / 2 := by unfold u; push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * t)]; ring
      have c7 : ((3 * t : ℕ) : ℚ) = ((u : ℚ) - 1) / 2 := by unfold u; push_cast; ring
      have c8 : ((3 * t + 1 : ℕ) : ℚ) = ((u : ℚ) + 1) / 2 := by unfold u; push_cast; ring
      have c9 : ((3 * t + 2 : ℕ) : ℚ) = ((u : ℚ) + 3) / 2 := by unfold u; push_cast; ring
      have c10 : ((6 * t - 2 : ℕ) : ℚ) = (u : ℚ) - 3 := by unfold u; push_cast [Nat.cast_sub (by omega : 2 ≤ 6 * t)]; ring
      have c11 : ((6 * t - 1 : ℕ) : ℚ) = (u : ℚ) - 2 := by unfold u; push_cast [Nat.cast_sub (by omega : 1 ≤ 6 * t)]; ring
      have c12 : ((6 * t : ℕ) : ℚ) = (u : ℚ) - 1 := by unfold u; push_cast; ring
      have c13 : ((6 * t + 2 : ℕ) : ℚ) = (u : ℚ) + 1 := by unfold u; push_cast; ring
      rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]
      simp only [inv_div, one_div]
      ring
    let P_m7 : ℤ := (u - 5) * (u - 4) * (u - 3) * (u - 2) * (u - 1) * (u + 1) * (u + 2) * (u + 3) * (u + 5)
    let P_m5 : ℤ := (u - 7) * (u - 4) * (u - 3) * (u - 2) * (u - 1) * (u + 1) * (u + 2) * (u + 3) * (u + 5)
    let P_m4 : ℤ := (u - 7) * (u - 5) * (u - 3) * (u - 2) * (u - 1) * (u + 1) * (u + 2) * (u + 3) * (u + 5)
    let P_m3 : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 2) * (u - 1) * (u + 1) * (u + 2) * (u + 3) * (u + 5)
    let P_m2 : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 3) * (u - 1) * (u + 1) * (u + 2) * (u + 3) * (u + 5)
    let P_m1 : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 3) * (u - 2) * (u + 1) * (u + 2) * (u + 3) * (u + 5)
    let P_p1 : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 3) * (u - 2) * (u - 1) * (u + 2) * (u + 3) * (u + 5)
    let P_p2 : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 3) * (u - 2) * (u - 1) * (u + 1) * (u + 3) * (u + 5)
    let P_p3 : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 3) * (u - 2) * (u - 1) * (u + 1) * (u + 2) * (u + 5)
    let P_p5 : ℤ := (u - 7) * (u - 5) * (u - 4) * (u - 3) * (u - 2) * (u - 1) * (u + 1) * (u + 2) * (u + 3)
    let A : ℤ := 3 * P_m7 + 2 * P_m5 + 3 * P_m4 + 3 * P_m3 + P_m2 + 3 * P_m1 + 3 * P_p1 + 3 * P_p2 + 2 * P_p3 + 3 * P_p5
    refine ⟨M, A, Q, hQ, ?_⟩
    rw [h_wpkt]
    have e_m7 : (M : ℚ) * (3 / ((u : ℚ) - 7)) = 3 * (P_m7 : ℚ) := by
      have hZ : M = (u - 7) * P_m7 := by unfold M P_m7; ring
      have hQ' : (M : ℚ) = ((u : ℚ) - 7) * (P_m7 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_m5 : (M : ℚ) * (2 / ((u : ℚ) - 5)) = 2 * (P_m5 : ℚ) := by
      have hZ : M = (u - 5) * P_m5 := by unfold M P_m5; ring
      have hQ' : (M : ℚ) = ((u : ℚ) - 5) * (P_m5 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_m4 : (M : ℚ) * (3 / ((u : ℚ) - 4)) = 3 * (P_m4 : ℚ) := by
      have hZ : M = (u - 4) * P_m4 := by unfold M P_m4; ring
      have hQ' : (M : ℚ) = ((u : ℚ) - 4) * (P_m4 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_m3 : (M : ℚ) * (3 / ((u : ℚ) - 3)) = 3 * (P_m3 : ℚ) := by
      have hZ : M = (u - 3) * P_m3 := by unfold M P_m3; ring
      have hQ' : (M : ℚ) = ((u : ℚ) - 3) * (P_m3 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_m2 : (M : ℚ) * (1 / ((u : ℚ) - 2)) = (P_m2 : ℚ) := by
      have hZ : M = (u - 2) * P_m2 := by unfold M P_m2; ring
      have hQ' : (M : ℚ) = ((u : ℚ) - 2) * (P_m2 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith), one_mul]
    have e_m1 : (M : ℚ) * (3 / ((u : ℚ) - 1)) = 3 * (P_m1 : ℚ) := by
      have hZ : M = (u - 1) * P_m1 := by unfold M P_m1; ring
      have hQ' : (M : ℚ) = ((u : ℚ) - 1) * (P_m1 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_p1 : (M : ℚ) * (3 / ((u : ℚ) + 1)) = 3 * (P_p1 : ℚ) := by
      have hZ : M = (u + 1) * P_p1 := by unfold M P_p1; ring
      have hQ' : (M : ℚ) = ((u : ℚ) + 1) * (P_p1 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_p2 : (M : ℚ) * (3 / ((u : ℚ) + 2)) = 3 * (P_p2 : ℚ) := by
      have hZ : M = (u + 2) * P_p2 := by unfold M P_p2; ring
      have hQ' : (M : ℚ) = ((u : ℚ) + 2) * (P_p2 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_p3 : (M : ℚ) * (2 / ((u : ℚ) + 3)) = 2 * (P_p3 : ℚ) := by
      have hZ : M = (u + 3) * P_p3 := by unfold M P_p3; ring
      have hQ' : (M : ℚ) = ((u : ℚ) + 3) * (P_p3 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    have e_p5 : (M : ℚ) * (3 / ((u : ℚ) + 5)) = 3 * (P_p5 : ℚ) := by
      have hZ : M = (u + 5) * P_p5 := by unfold M P_p5; ring
      have hQ' : (M : ℚ) = ((u : ℚ) + 5) * (P_p5 : ℚ) := by exact_mod_cast hZ
      rw [hQ', mul_div_left_comm, mul_div_cancel_left₀ _ (by linarith)]
    unfold A
    push_cast
    linear_combination e_m7 + e_m5 + e_m4 + e_m3 + e_m2 + e_m1 + e_p1 + e_p2 + e_p3 + e_p5

  have h_period : ∀ (N Y : ℕ) (P : Finset ℕ),
      475600 ≤ N → 151200000 * (2 * H₀ + 2) ≤ N → 1189 ≤ Y →
      N / 4800 ≤ P.card →
      (∀ t ∈ P, ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_pkt t).den = 1) →
      (∀ t ∈ P, w_pkt t ≤ 6000 / (1189 * (N : ℚ))) →
      let D := (Finset.Icc 1 Y).lcm id
      let L := D / 1189
      1189 * L = D ∧ 2 ∣ L ∧ 1 ≤ L ∧ 2 * H₀ + 2 ≤ L ∧
      Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ) ⊆
        Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1) := by
    intro N Y P hN hN_H hY hP_card hP_den hP_max D L
    have h2_mem : 2 ∈ Finset.Icc 1 Y := by simp; omega
    have h29_mem : 29 ∈ Finset.Icc 1 Y := by simp; omega
    have h41_mem : 41 ∈ Finset.Icc 1 Y := by simp; omega
    have h2_dvd : 2 ∣ D := Finset.dvd_lcm h2_mem
    have h29_dvd : 29 ∣ D := Finset.dvd_lcm h29_mem
    have h41_dvd : 41 ∣ D := Finset.dvd_lcm h41_mem
    have h58_dvd : 58 ∣ D := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2_dvd h29_dvd
    have h2378_dvd : 2378 ∣ D := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h58_dvd h41_dvd
    have hD_ne : D ≠ 0 := by
      unfold D
      rw [Finset.lcm_ne_zero_iff]
      intro x hx
      simp only [mem_Icc] at hx
      unfold id
      omega
    obtain ⟨m, hm⟩ := h2378_dvd
    have hm_ne : m ≠ 0 := by
      intro hm0
      apply hD_ne
      rw [hm, hm0, mul_zero]
    have hL_eq : L = 2 * m := by
      show D / 1189 = 2 * m
      rw [hm]
      omega
    have hL_mul : 1189 * L = D := by rw [hm, hL_eq]; ring
    have hL_even : 2 ∣ L := ⟨m, hL_eq⟩
    have hL_ge1 : 1 ≤ L := by omega
    have hP_pos : 0 < P.card := by omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hP_pos
    have h_w_nonneg : ∀ a b : ℕ, 0 ≤ w_Icc a b := by
      intro a b
      exact Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    have h_inv_le : ((6 * t + 1 : ℕ) : ℚ)⁻¹ ≤ w_pkt t := by
      have h_in : 6 * t + 1 ∈ Finset.Icc (6 * t - 2) (6 * t + 2) := by simp; omega
      have h_le_sub : ((6 * t + 1 : ℕ) : ℚ)⁻¹ ≤ w_Icc (6 * t - 2) (6 * t + 2) := by
        unfold w_Icc
        exact Finset.single_le_sum (f := fun n : ℕ => (n⁻¹ : ℚ)) (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)) h_in
      unfold w_pkt
      linarith [h_w_nonneg (2 * t - 2) (2 * t - 1), h_w_nonneg (2 * t + 1) (2 * t + 2),
        h_w_nonneg (3 * t - 2) (3 * t + 2)]
    have h_le_max := le_trans h_inv_le (hP_max t ht)
    have h_u_pos : (0 : ℚ) < ((6 * t + 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
    have h_N_pos : (0 : ℚ) < 1189 * (N : ℚ) := by positivity
    have h_N_le_t_q : 1189 * (N : ℚ) ≤ 6000 * ((6 * t + 1 : ℕ) : ℚ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ h_u_pos h_N_pos] at h_le_max
      linarith
    have h_N_le_t : 1189 * N ≤ 6000 * (6 * t + 1) := by exact_mod_cast h_N_le_t_q
    have ht_ge2 : 2 ≤ t := by omega
    obtain ⟨M, A, Q, hQ, hMA⟩ := h_elim t ht_ge2
    set K : ℤ := (((D : ℚ) * w_pkt t)).num
    have hK : (D : ℚ) * w_pkt t = (K : ℚ) := rat_eq_num_of_den_eq_one _ (hP_den t ht)
    have h_ident_q : (M : ℚ) * (K : ℚ) * ((6 * t + 1 : ℕ) : ℚ) - (M : ℚ) * (D : ℚ) =
        (D : ℚ) * ((6 * t + 1 : ℕ) : ℚ) * (A : ℚ) := by
      have h_mul := congrArg (fun x : ℚ => x * (D : ℚ) * ((6 * t + 1 : ℕ) : ℚ)) hMA
      dsimp only at h_mul
      have h_lhs : (M : ℚ) * (w_pkt t - ((6 * t + 1 : ℕ) : ℚ)⁻¹) * (D : ℚ) * ((6 * t + 1 : ℕ) : ℚ) =
          (M : ℚ) * ((D : ℚ) * w_pkt t) * ((6 * t + 1 : ℕ) : ℚ) -
          (M : ℚ) * (D : ℚ) * (((6 * t + 1 : ℕ) : ℚ)⁻¹ * ((6 * t + 1 : ℕ) : ℚ)) := by ring
      rw [h_lhs, hK, inv_mul_cancel₀ (ne_of_gt h_u_pos), mul_one] at h_mul
      linarith
    have h_ident_z : M * K * (6 * (t : ℤ) + 1) - M * (D : ℤ) =
        (D : ℤ) * (6 * (t : ℤ) + 1) * A := by exact_mod_cast h_ident_q
    set X : ℤ := M * K - Q * (D : ℤ) - (D : ℤ) * A
    have h_25200 : 25200 * (D : ℤ) = (6 * (t : ℤ) + 1) * X := by
      unfold X
      linear_combination -h_ident_z - (D : ℤ) * hQ
    have hD_pos_z : (0 : ℤ) < (D : ℤ) := Nat.cast_pos.mpr (by rw [hm]; omega)
    have hu_pos_z : (0 : ℤ) < 6 * (t : ℤ) + 1 := by omega
    have hX_pos : (0 : ℤ) < X := by nlinarith
    have hX_ge1 : (1 : ℤ) ≤ X := by omega
    have hu_le_z : 6 * (t : ℤ) + 1 ≤ 25200 * (D : ℤ) := by nlinarith
    have hu_le_nat : 6 * t + 1 ≤ 25200 * (1189 * L) := by
      rw [hL_mul]
      exact_mod_cast hu_le_z
    have hL_bound : 2 * H₀ + 2 ≤ L := by
      rw [hL_eq] at hu_le_nat ⊢
      omega
    refine ⟨hL_mul, hL_even, hL_ge1, hL_bound, ?_⟩
    intro x hx
    simp only [mem_Icc] at hx ⊢
    rw [hL_eq] at hL_bound ⊢
    omega

  have h_cos_prod : ∀ (l₀ : ℕ) (U : Finset (Fin l₀)) (α : Fin l₀ → ℝ) (θ₀ : ℝ),
      ∑ S ∈ U.powerset, Real.cos (θ₀ + 2 * ∑ i ∈ S, α i) =
        (2 : ℝ) ^ U.card * Real.cos (θ₀ + ∑ i ∈ U, α i) * ∏ i ∈ U, Real.cos (α i) := by
    intro l₀ U α θ₀
    induction U using Finset.induction_on generalizing θ₀ with
    | empty =>
      simp
    | @insert j V hj ih =>
      rw [Finset.powerset_insert]
      have h_disj : Disjoint V.powerset (V.powerset.image (insert j)) := by
        rw [Finset.disjoint_left]
        intro S hS hS_img
        rcases Finset.mem_image.mp hS_img with ⟨T, _, rfl⟩
        exact hj (Finset.mem_powerset.mp hS (Finset.mem_insert_self j T))
      have h_inj : ∀ S₁ ∈ V.powerset, ∀ S₂ ∈ V.powerset, insert j S₁ = insert j S₂ → S₁ = S₂ := by
        intro S₁ hS₁ S₂ hS₂ h_eq
        have hj₁ : j ∉ S₁ := fun h => hj (Finset.mem_powerset.mp hS₁ h)
        have hj₂ : j ∉ S₂ := fun h => hj (Finset.mem_powerset.mp hS₂ h)
        ext x
        constructor
        · intro hx
          have hx_ins : x ∈ insert j S₂ := h_eq ▸ Finset.mem_insert_of_mem hx
          rcases Finset.mem_insert.mp hx_ins with rfl | hx₂
          · exact False.elim (hj₁ hx)
          · exact hx₂
        · intro hx
          have hx_ins : x ∈ insert j S₁ := h_eq.symm ▸ Finset.mem_insert_of_mem hx
          rcases Finset.mem_insert.mp hx_ins with rfl | hx₁
          · exact False.elim (hj₂ hx)
          · exact hx₁
      rw [Finset.sum_union h_disj, Finset.sum_image h_inj]
      have h_img_eq : ∑ T ∈ V.powerset, Real.cos (θ₀ + 2 * ∑ i ∈ insert j T, α i) =
          ∑ T ∈ V.powerset, Real.cos ((θ₀ + 2 * α j) + 2 * ∑ i ∈ T, α i) := by
        refine Finset.sum_congr rfl (fun T hT => ?_)
        have hjT : j ∉ T := fun h => hj (Finset.mem_powerset.mp hT h)
        rw [Finset.sum_insert hjT]
        ring_nf
      rw [h_img_eq, ih θ₀, ih (θ₀ + 2 * α j)]
      rw [Finset.card_insert_of_notMem hj, Finset.sum_insert hj, Finset.prod_insert hj, pow_succ]
      set ψ := θ₀ + α j + ∑ i ∈ V, α i
      have h_a1 : θ₀ + ∑ i ∈ V, α i = ψ - α j := by unfold ψ; ring
      have h_a2 : θ₀ + 2 * α j + ∑ i ∈ V, α i = ψ + α j := by unfold ψ; ring
      have h_a3 : θ₀ + (α j + ∑ i ∈ V, α i) = ψ := by unfold ψ; ring
      rw [h_a1, h_a2, h_a3, Real.cos_sub ψ (α j), Real.cos_add ψ (α j)]
      ring

  have sum_Icc_int_eq_sum_range : ∀ (L : ℕ) (m : ℤ) (g : ℤ → ℝ),
      ∑ a ∈ Finset.Icc m (m + (L : ℤ) - 1), g a = ∑ k ∈ Finset.range L, g (m + (k : ℤ)) := by
    intro L m g
    induction L with
    | zero =>
      have h_empty : Finset.Icc m (m + (0 : ℕ) - 1) = ∅ := by
        ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
      rw [h_empty, range_zero, sum_empty, sum_empty]
    | succ n ih =>
      have h_ins : Finset.Icc m (m + ((n + 1 : ℕ) : ℤ) - 1) =
          insert (m + (n : ℤ)) (Finset.Icc m (m + (n : ℤ) - 1)) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      have h_notMem : m + (n : ℤ) ∉ Finset.Icc m (m + (n : ℤ) - 1) := by
        simp only [mem_Icc]; omega
      rw [h_ins, sum_insert h_notMem, ih, sum_range_succ]
      ring

  have telescope_cos_range : ∀ (n : ℕ) (m : ℝ) (θ : ℝ),
      2 * Real.sin θ * ∑ k ∈ Finset.range n, Real.cos (2 * (m + (k : ℝ)) * θ) =
        Real.sin ((2 * m + 2 * (n : ℝ) - 1) * θ) - Real.sin ((2 * m - 1) * θ) := by
    intro n m θ
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [sum_range_succ, mul_add, ih]
      have h1 : (2 * m + 2 * ((k + 1 : ℕ) : ℝ) - 1) * θ = (2 * (m + (k : ℝ)) * θ) + θ := by
        push_cast; ring
      have h2 : (2 * m + 2 * (k : ℝ) - 1) * θ = (2 * (m + (k : ℝ)) * θ) - θ := by
        ring
      rw [h1, h2, Real.sin_add, Real.sin_sub]
      ring

  have h_ortho : ∀ (L : ℕ) (z : ℤ),
      1 ≤ L → 2 ∣ L → 0 < z → z < 2 * (L : ℤ) → z ≠ (L : ℤ) →
      ∑ a ∈ Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1),
        Real.cos (2 * Real.pi * (a : ℝ) * (z : ℝ) / (L : ℝ)) = 0 := by
    intro L z hL hL_even hz_pos hz_lt hz_ne
    set m : ℤ := -(L : ℤ) / 2
    have hM : ((L : ℤ) + 1) / 2 - 1 = m + (L : ℤ) - 1 := by unfold m; omega
    rw [hM, sum_Icc_int_eq_sum_range]
    set θ : ℝ := Real.pi * (z : ℝ) / (L : ℝ)
    have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (by omega)
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    have h_rew : ∑ k ∈ Finset.range L, Real.cos (2 * Real.pi * ((m + (k : ℤ) : ℤ) : ℝ) * (z : ℝ) / (L : ℝ)) =
        ∑ k ∈ Finset.range L, Real.cos (2 * ((m : ℝ) + (k : ℝ)) * θ) := by
      refine sum_congr rfl (fun k _ => ?_)
      congr 1
      unfold θ
      push_cast
      ring
    rw [h_rew]
    have h_tele := telescope_cos_range L (m : ℝ) θ
    have h_period : (2 * (m : ℝ) + 2 * (L : ℝ) - 1) * θ = (2 * (m : ℝ) - 1) * θ + (z : ℝ) * (2 * Real.pi) := by
      unfold θ
      field_simp [hL_ne]
      ring
    rw [h_period, Real.sin_add_int_mul_two_pi, sub_self] at h_tele
    have h_sin_ne : Real.sin θ ≠ 0 := by
      rcases lt_or_gt_of_ne hz_ne with h_lt | h_gt
      · have hθ_pos : 0 < θ := by
          unfold θ
          have : (0 : ℝ) < (z : ℝ) := Int.cast_pos.mpr hz_pos
          positivity
        have hθ_lt : θ < Real.pi := by
          unfold θ
          rw [div_lt_iff₀ hL_pos]
          have : (z : ℝ) < (L : ℝ) := by exact_mod_cast h_lt
          nlinarith [Real.pi_pos]
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt)
      · have hθ_sub_pos : 0 < θ - Real.pi := by
          unfold θ
          rw [sub_pos, lt_div_iff₀ hL_pos]
          have : (L : ℝ) < (z : ℝ) := by exact_mod_cast h_gt
          nlinarith [Real.pi_pos]
        have hθ_sub_lt : θ - Real.pi < Real.pi := by
          unfold θ
          rw [sub_lt_iff_lt_add, div_lt_iff₀ hL_pos]
          have : (z : ℝ) < 2 * (L : ℝ) := by exact_mod_cast hz_lt
          nlinarith [Real.pi_pos]
        have h_sin_eq : Real.sin θ = -Real.sin (θ - Real.pi) := by
          rw [← Real.sin_add_pi (θ - Real.pi), sub_add_cancel]
        rw [h_sin_eq, neg_ne_zero]
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ_sub_pos hθ_sub_lt)
    have h2_ne : 2 * Real.sin θ ≠ 0 := mul_ne_zero two_ne_zero h_sin_ne
    exact (mul_eq_zero.mp h_tele).resolve_left h2_ne

  have abs_prod_cos_le_one : ∀ (l₀ : ℕ) (s : Finset (Fin l₀)) (g : Fin l₀ → ℝ),
      |∏ i ∈ s, Real.cos (g i)| ≤ 1 := by
    intro l₀ s g
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => Real.abs_cos_le_one _)

  have h_shifted : ∀ (L l₀ : ℕ) (P_T : ℝ) (r : Fin l₀ → ℝ),
      |P_T - (1 - (x_d : ℝ))| ≤ (g₀ : ℝ) / (40 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1)) →
      Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ) ⊆
        Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1) →
      (3 / 4 * (g₀ : ℝ) ≤
        ∑ a ∈ Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ),
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ))) *
            ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)) →
      (∑ a ∈ (Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1)) \
          (Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ)),
          (∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)|) ≤
        1 / 4 * (g₀ : ℝ)) →
      0 < ∑ a ∈ Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1),
        Real.cos (2 * Real.pi * (a : ℝ) * P_T + Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i) *
          ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i) := by
    intro L l₀ P_T r h_err h_sub h_low h_high
    have hg₀ : (0 : ℝ) < (g₀ : ℝ) := by exact_mod_cast hg₀_pos
    set I_low := Finset.Icc (-(H₀ : ℤ)) (H₀ : ℤ)
    set I_all := Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1)
    set f : ℤ → ℝ := fun a =>
      Real.cos (2 * Real.pi * (a : ℝ) * P_T + Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i) *
        ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)
    set f₀ : ℤ → ℝ := fun a =>
      Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ))) *
        ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)
    have h_split : ∑ a ∈ I_all, f a = ∑ a ∈ I_all \ I_low, f a + ∑ a ∈ I_low, f a :=
      (Finset.sum_sdiff h_sub).symm
    have h_tail : -(1 / 4 * (g₀ : ℝ)) ≤ ∑ a ∈ I_all \ I_low, f a := by
      have h1 : ∑ a ∈ I_all \ I_low, -(∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)|) ≤
          ∑ a ∈ I_all \ I_low, f a := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        have h_abs : |f a| ≤ ∏ i : Fin l₀, |Real.cos (Real.pi * (a : ℝ) * r i)| := by
          unfold f
          rw [abs_mul, Finset.abs_prod]
          exact mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (Real.abs_cos_le_one _)
        linarith [neg_abs_le (f a)]
      rw [Finset.sum_neg_distrib] at h1
      linarith
    have hH₀_pos : (0 : ℝ) < (H₀ : ℝ) := Nat.cast_pos.mpr (by omega)
    have h2H₀_pos : (0 : ℝ) < 2 * (H₀ : ℝ) + 1 := by positivity
    have h_head_term : ∀ a ∈ I_low, f₀ a - (g₀ : ℝ) / (5 * (2 * (H₀ : ℝ) + 1)) ≤ f a := by
      intro a ha
      have ha_bounds : -(H₀ : ℤ) ≤ a ∧ a ≤ (H₀ : ℤ) := Finset.mem_Icc.mp ha
      have ha_abs : |(a : ℝ)| ≤ (H₀ : ℝ) := by
        rw [abs_le]
        constructor <;> exact_mod_cast (by omega)
      have h_angle : 2 * Real.pi * (a : ℝ) * P_T + Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i =
          (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ)) +
            2 * Real.pi * (a : ℝ) * (P_T - (1 - (x_d : ℝ)))) + (a : ℝ) * (2 * Real.pi) := by ring
      have h_cos_eq : Real.cos (2 * Real.pi * (a : ℝ) * P_T + Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i) =
          Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ)) +
            2 * Real.pi * (a : ℝ) * (P_T - (1 - (x_d : ℝ)))) := by
        rw [h_angle, Real.cos_add_int_mul_two_pi]
      have h_diff_le : |f a - f₀ a| ≤ (g₀ : ℝ) / (5 * (2 * (H₀ : ℝ) + 1)) := by
        unfold f f₀
        rw [← sub_mul, abs_mul, h_cos_eq]
        have h_prod_le := abs_prod_cos_le_one l₀ Finset.univ (fun i : Fin l₀ => Real.pi * (a : ℝ) * r i)
        have h_lip := Real.abs_cos_sub_cos_le
          (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ)) + 2 * Real.pi * (a : ℝ) * (P_T - (1 - (x_d : ℝ))))
          (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ)))
        rw [add_sub_cancel_left, abs_mul, abs_mul, abs_of_pos Real.two_pi_pos] at h_lip
        have h_2pi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
        have h_bound1 : 2 * Real.pi * |(a : ℝ)| * |P_T - (1 - (x_d : ℝ))| ≤
            8 * (H₀ : ℝ) * ((g₀ : ℝ) / (40 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1))) := by
          have h_nonneg1 : 0 ≤ |(a : ℝ)| * |P_T - (1 - (x_d : ℝ))| := by positivity
          have h_step1 : 2 * Real.pi * (|(a : ℝ)| * |P_T - (1 - (x_d : ℝ))|) ≤ 8 * (|(a : ℝ)| * |P_T - (1 - (x_d : ℝ))|) :=
            mul_le_mul_of_nonneg_right h_2pi h_nonneg1
          have h_step2 : |(a : ℝ)| * |P_T - (1 - (x_d : ℝ))| ≤ (H₀ : ℝ) * ((g₀ : ℝ) / (40 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1))) :=
            mul_le_mul ha_abs h_err (abs_nonneg _) (le_of_lt hH₀_pos)
          linarith
        have h_eq_frac : 8 * (H₀ : ℝ) * ((g₀ : ℝ) / (40 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1))) =
            (g₀ : ℝ) / (5 * (2 * (H₀ : ℝ) + 1)) := by
          field_simp [ne_of_gt hH₀_pos, ne_of_gt h2H₀_pos]
          ring
        have h_cos_bound : |Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ)) +
            2 * Real.pi * (a : ℝ) * (P_T - (1 - (x_d : ℝ)))) -
            Real.cos (Real.pi * (a : ℝ) * ((∑ i : Fin l₀, r i) - 2 * (x_d : ℝ)))| ≤
            (g₀ : ℝ) / (5 * (2 * (H₀ : ℝ) + 1)) := by
          linarith
        exact le_trans (mul_le_of_le_one_right (abs_nonneg _) h_prod_le) h_cos_bound
      linarith [neg_abs_le (f a - f₀ a)]
    have h_sum_head := Finset.sum_le_sum h_head_term
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h_sum_head
    have h_card : (I_low.card : ℝ) = 2 * (H₀ : ℝ) + 1 := by
      unfold I_low
      rw [Int.card_Icc]
      have : ((H₀ : ℤ) + 1 - -(H₀ : ℤ)).toNat = 2 * H₀ + 1 := by omega
      rw [this]
      push_cast
      ring
    rw [h_card] at h_sum_head
    have h_cancel : (2 * (H₀ : ℝ) + 1) * ((g₀ : ℝ) / (5 * (2 * (H₀ : ℝ) + 1))) = 1 / 5 * (g₀ : ℝ) := by
      field_simp [ne_of_gt h2H₀_pos]
    rw [h_cancel] at h_sum_head
    linarith

  let B_g : ℕ := Nat.ceil ((240000 * (H₀ : ℚ) * (2 * (H₀ : ℚ) + 1)) / g₀)
  let N_four : ℕ := max 475600 (max (151200000 * (2 * H₀ + 2)) B_g)
  refine ⟨N_four, le_max_left _ _, ?_⟩
  intro N hN Y hY _ l₀ R₀ hWR₀_le hR₀_den h_low_freq h_high_freq P hP_den hP_card hP_max hP_sum_low _
  have hN_475600 : 475600 ≤ N := by omega
  have hN_H : 151200000 * (2 * H₀ + 2) ≤ N := by omega
  have hN_Bg : B_g ≤ N := by omega
  set δ : ℚ := 6000 / (1189 * (N : ℚ))
  set τ : ℚ := (1 - x_d) / 1189
  have hδ_pos : 0 < δ := by unfold δ; positivity
  have hτ_nonneg : 0 ≤ τ := by unfold τ; linarith
  have hτ_le_sum : τ ≤ ∑ t ∈ P, w_pkt t := by unfold τ; linarith
  obtain ⟨T, hT_sub, hT_low, hT_high⟩ := h_greedy P δ τ hP_max hδ_pos hτ_nonneg hτ_le_sum
  set D : ℕ := (Finset.Icc 1 Y).lcm id
  set L : ℕ := D / 1189
  obtain ⟨hL_mul, hL_even, hL_ge1, _, h_sub_Icc⟩ :=
    h_period N Y P hN_475600 hN_H hY hP_card hP_den hP_max
  set S_T : ℚ := ∑ t ∈ T, w_pkt t
  set P_T : ℝ := 1189 * (S_T : ℝ)
  set r : Fin l₀ → ℝ := fun i => 1189 * (w_Icc (R₀ i).1 (R₀ i).2 : ℝ)
  have h_PT_err : |P_T - (1 - (x_d : ℝ))| ≤ (g₀ : ℝ) / (40 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1)) := by
    have h_diff_q1 : (1 - x_d) - 6000 / (N : ℚ) ≤ 1189 * S_T := by
      have : (1 - x_d) - 6000 / (N : ℚ) = 1189 * (τ - δ) := by unfold τ δ; ring
      change τ - δ ≤ S_T at hT_low
      linarith
    have h_diff_q2 : 1189 * S_T ≤ 1 - x_d := by
      have : 1 - x_d = 1189 * τ := by unfold τ; ring
      change S_T ≤ τ at hT_high
      linarith
    have h_diff_r1 : (1 - (x_d : ℝ)) - 6000 / (N : ℝ) ≤ P_T := by
      have h_c : (((1 - x_d) - 6000 / (N : ℚ) : ℚ) : ℝ) ≤ ((1189 * S_T : ℚ) : ℝ) := by
        exact_mod_cast h_diff_q1
      push_cast at h_c
      exact h_c
    have h_diff_r2 : P_T ≤ 1 - (x_d : ℝ) := by
      have h_c : ((1189 * S_T : ℚ) : ℝ) ≤ ((1 - x_d : ℚ) : ℝ) := by
        exact_mod_cast h_diff_q2
      push_cast at h_c
      exact h_c
    have h_abs_6000 : |P_T - (1 - (x_d : ℝ))| ≤ 6000 / (N : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    have h_Bg_cast : (B_g : ℚ) ≤ (N : ℚ) := Nat.cast_le.mpr hN_Bg
    have h_Bg_q : (240000 * (H₀ : ℚ) * (2 * (H₀ : ℚ) + 1)) / g₀ ≤ (N : ℚ) :=
      le_trans (Nat.le_ceil _) h_Bg_cast
    have h_Bg_r : (240000 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1)) / (g₀ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast h_Bg_q
    have hg₀_r : (0 : ℝ) < (g₀ : ℝ) := by exact_mod_cast hg₀_pos
    have hH₀_r : (0 : ℝ) < 40 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1) := by positivity
    have hN_r : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    have h_6000_le : 6000 / (N : ℝ) ≤ (g₀ : ℝ) / (40 * (H₀ : ℝ) * (2 * (H₀ : ℝ) + 1)) := by
      rw [div_le_div_iff₀ hN_r hH₀_r]
      rw [div_le_iff₀ hg₀_r] at h_Bg_r
      linarith
    exact le_trans h_abs_6000 h_6000_le
  have h_pos_sum := h_shifted L l₀ P_T r h_PT_err h_sub_Icc h_low_freq h_high_freq
  set I_all := Finset.Icc (-(L : ℤ) / 2) (((L : ℤ) + 1) / 2 - 1)
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ l₀ := by positivity
  have h_mul_pos : 0 < (2 : ℝ) ^ l₀ * ∑ a ∈ I_all,
      Real.cos (2 * Real.pi * (a : ℝ) * P_T + Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i) *
        ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i) :=
    mul_pos h_pow_pos h_pos_sum
  rw [Finset.mul_sum] at h_mul_pos
  have h_eq_powerset : ∑ a ∈ I_all, (2 : ℝ) ^ l₀ *
      (Real.cos (2 * Real.pi * (a : ℝ) * P_T + Real.pi * (a : ℝ) * ∑ i : Fin l₀, r i) *
        ∏ i : Fin l₀, Real.cos (Real.pi * (a : ℝ) * r i)) =
      ∑ S ∈ (Finset.univ : Finset (Fin l₀)).powerset,
        ∑ a ∈ I_all, Real.cos (2 * Real.pi * (a : ℝ) * P_T + 2 * ∑ i ∈ S, (Real.pi * (a : ℝ) * r i)) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h_cp := h_cos_prod l₀ Finset.univ (fun i => Real.pi * (a : ℝ) * r i) (2 * Real.pi * (a : ℝ) * P_T)
    simp only [Finset.card_univ, Fintype.card_fin] at h_cp
    rw [← Finset.mul_sum] at h_cp
    rw [h_cp]
    ring
  rw [h_eq_powerset] at h_mul_pos
  have h_exists_S : ∃ S ∈ (Finset.univ : Finset (Fin l₀)).powerset,
      ∑ a ∈ I_all, Real.cos (2 * Real.pi * (a : ℝ) * P_T + 2 * ∑ i ∈ S, (Real.pi * (a : ℝ) * r i)) ≠ 0 := by
    by_contra! h_all_zero
    have h_zero : ∑ S ∈ (Finset.univ : Finset (Fin l₀)).powerset,
        ∑ a ∈ I_all, Real.cos (2 * Real.pi * (a : ℝ) * P_T + 2 * ∑ i ∈ S, (Real.pi * (a : ℝ) * r i)) = 0 :=
      Finset.sum_eq_zero h_all_zero
    linarith
  obtain ⟨S, _, hS_ne⟩ := h_exists_S
  refine ⟨T, S, hT_sub, ?_⟩
  set W : ℚ := S_T + ∑ i ∈ S, w_Icc (R₀ i).1 (R₀ i).2
  set z : ℤ := (∑ t ∈ T, (((D : ℚ) * w_pkt t)).num) +
    (∑ i ∈ S, (((D : ℚ) * w_Icc (R₀ i).1 (R₀ i).2)).num)
  have hDW : (D : ℚ) * W = (z : ℚ) := by
    unfold W S_T z
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    push_cast
    congr 1
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      exact rat_eq_num_of_den_eq_one _ (hP_den t (hT_sub ht))
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      exact rat_eq_num_of_den_eq_one _ (hR₀_den i)
  have hLW : 1189 * (L : ℚ) * W = (z : ℚ) := by
    have hD_cast : (D : ℚ) = 1189 * (L : ℚ) := by exact_mod_cast hL_mul.symm
    rw [← hD_cast, hDW]
  have h_w_nonneg : ∀ a b : ℕ, 0 ≤ w_Icc a b := by
    intro a b
    exact Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  have hS_nonneg : 0 ≤ ∑ i ∈ S, w_Icc (R₀ i).1 (R₀ i).2 :=
    Finset.sum_nonneg (fun i _ => h_w_nonneg (R₀ i).1 (R₀ i).2)
  have hS_le_all : ∑ i ∈ S, w_Icc (R₀ i).1 (R₀ i).2 ≤ 1 / 118900 := by
    have h_sub_univ : ∑ i ∈ S, w_Icc (R₀ i).1 (R₀ i).2 ≤ ∑ i : Fin l₀, w_Icc (R₀ i).1 (R₀ i).2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => h_w_nonneg (R₀ i).1 (R₀ i).2)
    exact le_trans h_sub_univ hWR₀_le
  have hW_pos : 0 < W := by
    have h_N_ge_q : (475600 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN_475600
    have hδ_le : δ ≤ 6000 / (1189 * 475600) := by
      unfold δ
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    change τ - δ ≤ S_T at hT_low
    unfold W τ at *
    linarith
  have hW_lt : W < 2 / 1189 := by
    change S_T ≤ τ at hT_high
    unfold W τ at *
    linarith
  have hL_pos_q : (0 : ℚ) < (L : ℚ) := Nat.cast_pos.mpr hL_ge1
  have hz_pos_q : (0 : ℚ) < (z : ℚ) := by
    rw [← hLW]
    positivity
  have hz_pos : 0 < z := by exact_mod_cast hz_pos_q
  have hz_lt_q : (z : ℚ) < 2 * (L : ℚ) := by
    rw [← hLW]
    nlinarith
  have hz_lt : z < 2 * (L : ℤ) := by exact_mod_cast hz_lt_q
  have h_cos_rewrite : ∑ a ∈ I_all, Real.cos (2 * Real.pi * (a : ℝ) * P_T + 2 * ∑ i ∈ S, (Real.pi * (a : ℝ) * r i)) =
      ∑ a ∈ I_all, Real.cos (2 * Real.pi * (a : ℝ) * (z : ℝ) / (L : ℝ)) := by
    have hLW_r : 1189 * (L : ℝ) * (W : ℝ) = (z : ℝ) := by exact_mod_cast hLW
    have hW_r : 1189 * (W : ℝ) = P_T + ∑ i ∈ S, r i := by
      unfold W P_T S_T r
      push_cast
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    have hL_ne_r : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [← Finset.mul_sum]
    rw [eq_div_iff hL_ne_r]
    calc (2 * Real.pi * (a : ℝ) * P_T + 2 * (Real.pi * (a : ℝ) * ∑ i ∈ S, r i)) * (L : ℝ)
      _ = 2 * Real.pi * (a : ℝ) * (P_T + ∑ i ∈ S, r i) * (L : ℝ) := by ring
      _ = 2 * Real.pi * (a : ℝ) * (1189 * (L : ℝ) * (W : ℝ)) := by rw [← hW_r]; ring
      _ = 2 * Real.pi * (a : ℝ) * (z : ℝ) := by rw [hLW_r]
  have hz_eq_L : z = (L : ℤ) := by
    by_contra hz_ne
    have h_zero := h_ortho L z hL_ge1 hL_even hz_pos hz_lt hz_ne
    rw [h_cos_rewrite] at hS_ne
    exact hS_ne h_zero
  have hLW_eq : 1189 * (L : ℚ) * W = (L : ℚ) := by
    rw [hLW, hz_eq_L]
    simp
  have hL_ne_q : (L : ℚ) ≠ 0 := ne_of_gt hL_pos_q
  calc W = (1189 * (L : ℚ) * W) / (1189 * (L : ℚ)) := by
         field_simp [hL_ne_q]
    _ = (L : ℚ) / (1189 * (L : ℚ)) := by rw [hLW_eq]
    _ = 1 / 1189 := by field_simp [hL_ne_q]

theorem coherent_reserve_and_subset_sum_compiler (h_pool : ∀ (ε : ℚ), 0 < ε →
      ∃ N₁ : ℕ, 475600 ≤ N₁ ∧ ∀ N ≥ N₁, ∀ Y : ℕ,
        Y ^ 512 ≤ N ^ 511 → N ^ 511 < (Y + 1) ^ 512 →
        ∀ (l₀ : ℕ) (R₀ : Fin l₀ → ℕ × ℕ),
          l₀ ≤ N / (Nat.ceil (30000 / ε) + 237800) →
          (∀ i : Fin l₀, (R₀ i).2 ≤ (R₀ i).1 + 2) →
          ∃ P : Finset ℕ, P ⊆ Finset.Icc N ((9 * N) / 8) ∧
            (∀ t ∈ P, 3 ∣ t) ∧
            (∀ i : Fin l₀, ∀ t ∈ P,
              ((R₀ i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (R₀ i).1) ∧
              ((R₀ i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (R₀ i).1) ∧
              ((R₀ i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (R₀ i).1)) ∧
            (∀ t ∈ P, ((((Finset.Icc 1 Y).lcm id : ℕ) : ℚ) * w_pkt t).den = 1) ∧
            N / 4800 ≤ P.card ∧
            (∀ t ∈ P, w_pkt t ≤ 6000 / (1189 * (N : ℚ))) ∧
            3 / 2 - ε ≤ 1189 * ∑ t ∈ P, w_pkt t ∧
            1189 * ∑ t ∈ P, w_pkt t ≤ 3 / 2 + ε) :
    ∃ N₀ : ℕ, 475600 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∃ T : Finset ℕ, T ⊆ Finset.Icc N ((9 * N) / 8) ∧ (∀ t ∈ T, 3 ∣ t) ∧
      ∃ (l : ℕ) (R : Fin l → ℕ × ℕ),
        (∀ i : Fin l, 495 ≤ (R i).1 ∧ (R i).1 < (R i).2) ∧
        (∀ i j : Fin l, i ≠ j → (R i).2 + 1 < (R j).1 ∨ (R j).2 + 1 < (R i).1) ∧
        (∀ i : Fin l, ∀ t ∈ T,
          ((R i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (R i).1) ∧
          ((R i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (R i).1) ∧
          ((R i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (R i).1)) ∧
        (∑ t ∈ T, w_pkt t + ∑ i : Fin l, w_Icc (R i).1 (R i).2 = 1 / 1189) ∧
        59450 * (l + 4) ≤ N ∧
        ∑ i : Fin l, w_Icc (R i).1 (R i).2 ≤ 1 / 118900 :=
by
  classical
  obtain ⟨Y₀, H₀, l_seq, R_seq, x_d, g₀, hY₀_1189, hH₀_1, hxd_pos, hxd_lt, hg₀_pos, h_prof⟩ :=
    coherent_reserve_fourier_profile_existence
  obtain ⟨N_four, hN_four_475600, h_four⟩ :=
    finite_fourier_subset_sum_extraction H₀ x_d g₀ hH₀_1 hxd_pos hxd_lt hg₀_pos
  obtain ⟨N₁, hN₁_475600, h_pool_eps⟩ := h_pool (1 / 10) (by norm_num)
  let N₀ := max 475600 (max N₁ (max N_four (Y₀ ^ 2 + 1)))
  refine ⟨N₀, by omega, fun N hN => ?_⟩
  
  have h_ex_Y : ∃ k : ℕ, N ^ 511 < (k + 1) ^ 512 := by
    refine ⟨N, ?_⟩
    have h1 : N ^ 511 < (N + 1) ^ 511 := (Nat.pow_lt_pow_iff_left (by decide)).mpr (by omega)
    have h2 : (N + 1) ^ 511 ≤ (N + 1) ^ 512 := Nat.pow_le_pow_right (by omega) (by decide)
    exact lt_of_lt_of_le h1 h2
  let Y := Nat.find h_ex_Y
  have hY_upper : N ^ 511 < (Y + 1) ^ 512 := Nat.find_spec h_ex_Y
  have hY_lower : Y ^ 512 ≤ N ^ 511 := by
    rcases eq_or_ne Y 0 with hY0 | hY_pos
    · rw [hY0]; simp
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hY_pos
      have hm_lt : m < Y := by omega
      have h_min : (m + 1) ^ 512 ≤ N ^ 511 := not_lt.mp (Nat.find_min h_ex_Y hm_lt)
      rw [hm, Nat.succ_eq_add_one]
      exact h_min
  have hY₀_le : Y₀ ≤ Y := by
    have hN_gt : Y₀ ^ 2 < N := by omega
    have h_pow1 : (Y₀ ^ 2) ^ 511 ≤ N ^ 511 := Nat.pow_le_pow_left (by omega) 511
    have h_pow2 : Y₀ ^ 512 ≤ (Y₀ ^ 2) ^ 511 := by
      rw [← Nat.pow_mul]
      rcases eq_or_ne Y₀ 0 with rfl | hY₀_pos
      · simp
      · exact Nat.pow_le_pow_right (by omega) (by decide)
    have h_lt : Y₀ ^ 512 < (Y + 1) ^ 512 := lt_of_le_of_lt (le_trans h_pow2 h_pow1) hY_upper
    have h_lt_base : Y₀ < Y + 1 := (Nat.pow_lt_pow_iff_left (by decide)).mp h_lt
    omega
  
  obtain ⟨hR₀_bounds, hR₀_sep, hWR₀_le, hl₀_scale, hR₀_den, h_low_freq, h_high_freq⟩ := h_prof Y hY₀_le
  let l₀ := l_seq Y
  let R₀ := R_seq Y
  have hl₀_bound : 537800 * (l₀ + 4) ≤ N := hl₀_scale N hY_lower
  have h_ceil : Nat.ceil (30000 / (1 / 10 : ℚ)) + 237800 = 537800 := by
    norm_num
  have hl₀_div : l₀ ≤ N / (Nat.ceil (30000 / (1 / 10 : ℚ)) + 237800) := by
    rw [h_ceil, Nat.le_div_iff_mul_le (by omega)]
    omega
  
  obtain ⟨P, hP_sub, hP_div, hRP_sep, hP_den, hP_card, hP_max, hP_sum_low, hP_sum_high⟩ :=
    h_pool_eps N (by omega) Y hY_lower hY_upper l₀ R₀ hl₀_div (fun i => (hR₀_bounds i).2.2)
  
  obtain ⟨T, S, hT_sub_P, h_weight⟩ :=
    h_four N (by omega) Y (le_trans hY₀_1189 hY₀_le) hY_lower l₀ R₀ hWR₀_le hR₀_den h_low_freq h_high_freq
      P hP_den hP_card hP_max hP_sum_low hP_sum_high
  
  let l := S.card
  let e : Fin l ≃ {x // x ∈ S} := S.equivFin.symm
  let R : Fin l → ℕ × ℕ := fun i => R₀ (e i).1
  have h_sum_eq : ∑ i : Fin l, w_Icc (R i).1 (R i).2 = ∑ i ∈ S, w_Icc (R₀ i).1 (R₀ i).2 := by
    exact (Finset.sum_equiv e (by simp) (by simp [R])).trans
      (Finset.sum_attach S (fun i => w_Icc (R₀ i).1 (R₀ i).2))
  refine ⟨T, Finset.Subset.trans hT_sub_P hP_sub, fun t ht => hP_div t (hT_sub_P ht),
    l, R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hR₀_bounds (e i).1).1, (hR₀_bounds (e i).1).2.1⟩
  · intro i j hij
    apply hR₀_sep
    intro h_eq
    apply hij
    apply e.injective
    exact Subtype.ext h_eq
  · intro i t ht
    exact hRP_sep (e i).1 t (hT_sub_P ht)
  · rw [h_sum_eq]
    exact h_weight
  · have hl_le : l ≤ l₀ := by
      simpa [l] using Finset.card_le_univ S
    omega
  · rw [h_sum_eq]
    have h_sub_le : ∑ i ∈ S, w_Icc (R₀ i).1 (R₀ i).2 ≤ ∑ i : Fin l₀, w_Icc (R₀ i).1 (R₀ i).2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
      intro i _ _
      apply Finset.sum_nonneg
      intro n _
      exact inv_nonneg.mpr (Nat.cast_nonneg n)
    exact le_trans h_sub_le hWR₀_le

theorem scale_window_packet_reserve_existence : ∃ N₀ : ℕ, 39651 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∃ T : Finset ℕ, T ⊆ Finset.Icc N ((9 * N) / 8) ∧ (∀ t ∈ T, 3 ∣ t) ∧
      ∃ (l : ℕ) (R : Fin l → ℕ × ℕ),
        (∀ i : Fin l, 495 ≤ (R i).1 ∧ (R i).1 < (R i).2) ∧
        (∀ i j : Fin l, i ≠ j → (R i).2 + 1 < (R j).1 ∨ (R j).2 + 1 < (R i).1) ∧
        (∀ i : Fin l, ∀ t ∈ T,
          ((R i).2 + 1 < 2 * t - 2 ∨ 2 * t + 3 < (R i).1) ∧
          ((R i).2 + 1 < 3 * t - 2 ∨ 3 * t + 3 < (R i).1) ∧
          ((R i).2 + 1 < 6 * t - 2 ∨ 6 * t + 3 < (R i).1)) ∧
        (∑ t ∈ T, w_pkt t + ∑ i : Fin l, w_Icc (R i).1 (R i).2 = 1 / 1189) ∧
        4 + l + 4 * T.card ≤ (51 * N) / 59450 + 1 ∧
        (54 * N) / 59450 ≤ 4 + l + 5 * T.card :=
by
  have h_w_Icc_bounds : ∀ (a b L U : ℕ), 0 < L → L ≤ a → b ≤ U →
      ((b + 1 - a : ℕ) : ℚ) * (U : ℚ)⁻¹ ≤ w_Icc a b ∧
      w_Icc a b ≤ ((b + 1 - a : ℕ) : ℚ) * (L : ℚ)⁻¹ := by
    intro a b L U hL ha hb
    have hL_pos : (0 : ℚ) < (L : ℚ) := Nat.cast_pos.mpr hL
    constructor
    · have h1 : ∀ n ∈ Finset.Icc a b, (U : ℚ)⁻¹ ≤ (n : ℚ)⁻¹ := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        have hn_pos : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr (by omega)
        have hnU : (n : ℚ) ≤ (U : ℚ) := by exact_mod_cast (by omega : n ≤ U)
        exact inv_anti₀ hn_pos hnU
      have h2 := Finset.card_nsmul_le_sum (Finset.Icc a b) (fun n : ℕ => (n : ℚ)⁻¹) (U : ℚ)⁻¹ h1
      simpa [w_Icc, Nat.card_Icc, nsmul_eq_mul] using h2
    · have h1 : ∀ n ∈ Finset.Icc a b, (n : ℚ)⁻¹ ≤ (L : ℚ)⁻¹ := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        have hLn : (L : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : L ≤ n)
        exact inv_anti₀ hL_pos hLn
      have h2 := Finset.sum_le_card_nsmul (Finset.Icc a b) (fun n : ℕ => (n : ℚ)⁻¹) (L : ℚ)⁻¹ h1
      simpa [w_Icc, Nat.card_Icc, nsmul_eq_mul] using h2

  have h_pkt_bounds : ∀ t : ℕ, 2 ≤ t →
      9 / (2 * (t : ℚ) + 2) ≤ w_pkt t ∧ w_pkt t ≤ 9 / (2 * (t : ℚ) - 2) := by
    intro t ht
    have hb1 := h_w_Icc_bounds (2 * t - 2) (2 * t - 1) (2 * (t - 1)) (2 * (t + 1)) (by omega) (by omega) (by omega)
    have hb2 := h_w_Icc_bounds (2 * t + 1) (2 * t + 2) (2 * (t - 1)) (2 * (t + 1)) (by omega) (by omega) (by omega)
    have hb3 := h_w_Icc_bounds (3 * t - 2) (3 * t + 2) (3 * (t - 1)) (3 * (t + 1)) (by omega) (by omega) (by omega)
    have hb4 := h_w_Icc_bounds (6 * t - 2) (6 * t + 2) (6 * (t - 1)) (6 * (t + 1)) (by omega) (by omega) (by omega)
    have hc1 : 2 * t - 1 + 1 - (2 * t - 2) = 2 := by omega
    have hc2 : 2 * t + 2 + 1 - (2 * t + 1) = 2 := by omega
    have hc3 : 3 * t + 2 + 1 - (3 * t - 2) = 5 := by omega
    have hc4 : 6 * t + 2 + 1 - (6 * t - 2) = 5 := by omega
    rw [hc1] at hb1
    rw [hc2] at hb2
    rw [hc3] at hb3
    rw [hc4] at hb4
    have hcast_sub : ((t - 1 : ℕ) : ℚ) = (t : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    push_cast [hcast_sub] at hb1 hb2 hb3 hb4
    have h_eq_low : 2 * (2 * ((t : ℚ) + 1))⁻¹ + 2 * (2 * ((t : ℚ) + 1))⁻¹ +
        5 * (3 * ((t : ℚ) + 1))⁻¹ + 5 * (6 * ((t : ℚ) + 1))⁻¹ = 9 / (2 * (t : ℚ) + 2) := by
      have h_rew : (2 * (t : ℚ) + 2) = 2 * ((t : ℚ) + 1) := by ring
      rw [h_rew, div_eq_mul_inv]
      repeat rw [mul_inv]
      ring
    have h_eq_high : 2 * (2 * ((t : ℚ) - 1))⁻¹ + 2 * (2 * ((t : ℚ) - 1))⁻¹ +
        5 * (3 * ((t : ℚ) - 1))⁻¹ + 5 * (6 * ((t : ℚ) - 1))⁻¹ = 9 / (2 * (t : ℚ) - 2) := by
      have h_rew : (2 * (t : ℚ) - 2) = 2 * ((t : ℚ) - 1) := by ring
      rw [h_rew, div_eq_mul_inv]
      repeat rw [mul_inv]
      ring
    unfold w_pkt
    constructor <;> linarith

  obtain ⟨N₀, hN₀_475600, h_comp⟩ := coherent_reserve_and_subset_sum_compiler smooth_pruned_packet_pool_existence
  refine ⟨N₀, by omega, fun N hN => ?_⟩
  obtain ⟨T, hT_sub, hT_div, l, R, hR_bounds, hR_sep, hRT_sep, h_weight, hl_bound, hWR_le⟩ := h_comp N hN
  refine ⟨T, hT_sub, hT_div, l, R, hR_bounds, hR_sep, hRT_sep, h_weight, ?_⟩
  have hN_475600 : 475600 ≤ N := le_trans hN₀_475600 hN
  set WR : ℚ := ∑ i : Fin l, w_Icc (R i).1 (R i).2
  have hWR_nonneg : 0 ≤ WR := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro n _
    positivity
  have h_low_term : ∀ t ∈ T, 36 / (9 * (N : ℚ) + 8) ≤ w_pkt t := by
    intro t ht
    have ht_Icc := Finset.mem_Icc.mp (hT_sub ht)
    have ht_ge2 : 2 ≤ t := by omega
    have hpkt := (h_pkt_bounds t ht_ge2).1
    have h8t : (8 * t : ℕ) ≤ 9 * N := by omega
    have h8t_q : 8 * (t : ℚ) ≤ 9 * (N : ℚ) := by exact_mod_cast h8t
    have h_step : 36 / (9 * (N : ℚ) + 8) ≤ 9 / (2 * (t : ℚ) + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    exact le_trans h_step hpkt
  have h_sum_ge := Finset.card_nsmul_le_sum T w_pkt (36 / (9 * (N : ℚ) + 8)) h_low_term
  rw [nsmul_eq_mul] at h_sum_ge
  have h_sum_le_top : ∑ t ∈ T, w_pkt t ≤ 1 / 1189 := by linarith
  have h_card_top_div : (T.card : ℚ) * (36 / (9 * (N : ℚ) + 8)) ≤ 1 / 1189 :=
    le_trans h_sum_ge h_sum_le_top
  have h_card_top_q : (1189 * (36 * T.card) : ℚ) ≤ 9 * (N : ℚ) + 8 := by
    have h_pos : (0 : ℚ) < 9 * (N : ℚ) + 8 := by positivity
    have h_mul := mul_le_mul_of_nonneg_right h_card_top_div (le_of_lt h_pos)
    have h_cancel : (T.card : ℚ) * (36 / (9 * (N : ℚ) + 8)) * (9 * (N : ℚ) + 8) = (T.card : ℚ) * 36 := by
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt h_pos)]
    rw [h_cancel] at h_mul
    linarith
  have h_card_top_nat : 1189 * (36 * T.card) ≤ 9 * N + 8 := by exact_mod_cast h_card_top_q

  have h_high_term : ∀ t ∈ T, w_pkt t ≤ 9 / (2 * (N : ℚ) - 2) := by
    intro t ht
    have ht_Icc := Finset.mem_Icc.mp (hT_sub ht)
    have ht_ge2 : 2 ≤ t := by omega
    have hpkt := (h_pkt_bounds t ht_ge2).2
    have hNt_q : (N : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht_Icc.1
    have h_pos_N : (0 : ℚ) < 2 * (N : ℚ) - 2 := by
      have : (2 : ℚ) ≤ (N : ℚ) := by exact_mod_cast (by omega : 2 ≤ N)
      linarith
    have h_pos_t : (0 : ℚ) < 2 * (t : ℚ) - 2 := by linarith
    have h_step : 9 / (2 * (t : ℚ) - 2) ≤ 9 / (2 * (N : ℚ) - 2) := by
      rw [div_le_div_iff₀ h_pos_t h_pos_N]
      linarith
    exact le_trans hpkt h_step
  have h_sum_le := Finset.sum_le_card_nsmul T w_pkt (9 / (2 * (N : ℚ) - 2)) h_high_term
  rw [nsmul_eq_mul] at h_sum_le
  have h_sum_ge_bot : 99 / 118900 ≤ ∑ t ∈ T, w_pkt t := by linarith
  have h_card_bot_div : 99 / 118900 ≤ (T.card : ℚ) * (9 / (2 * (N : ℚ) - 2)) :=
    le_trans h_sum_ge_bot h_sum_le
  have h_card_bot_q : (11 * N : ℚ) ≤ (59450 * T.card + 11 : ℚ) := by
    have h_pos_N : (0 : ℚ) < 2 * (N : ℚ) - 2 := by
      have : (2 : ℚ) ≤ (N : ℚ) := by exact_mod_cast (by omega : 2 ≤ N)
      linarith
    have h_mul := mul_le_mul_of_nonneg_right h_card_bot_div (le_of_lt h_pos_N)
    have h_cancel : (T.card : ℚ) * (9 / (2 * (N : ℚ) - 2)) * (2 * (N : ℚ) - 2) = (T.card : ℚ) * 9 := by
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt h_pos_N)]
    rw [h_cancel] at h_mul
    linarith
  have h_card_bot_nat : 11 * N ≤ 59450 * T.card + 11 := by exact_mod_cast h_card_bot_q
  constructor <;> omega

theorem erdos_289 :
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
    ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) :=
by
  have hA_bounds : ∀ i : Fin 4, 2 ≤ (pellAnchor i).1 ∧ (pellAnchor i).1 < (pellAnchor i).2 ∧ (pellAnchor i).2 ≤ 493 := by
    decide
  have hA_sep : ∀ i j : Fin 4, i ≠ j → (pellAnchor i).2 + 1 < (pellAnchor j).1 ∨ (pellAnchor j).2 + 1 < (pellAnchor i).1 := by
    decide
  have hA_sum : ∑ i : Fin 4, w_Icc (pellAnchor i).1 (pellAnchor i).2 = 1188 / 1189 := by
    have h0 : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := rfl
    have h1 : Finset.Icc 14 15 = ({14, 15} : Finset ℕ) := rfl
    have h2 : Finset.Icc 84 85 = ({84, 85} : Finset ℕ) := rfl
    have h3 : Finset.Icc 492 493 = ({492, 493} : Finset ℕ) := rfl
    simp [Fin.sum_univ_four, pellAnchor, w_Icc, h0, h1, h2, h3]
    norm_num
  obtain ⟨N₀, hN₀, h_scale⟩ := scale_window_packet_reserve_existence
  have h_win : ∀ N ≥ N₀, ∀ k : ℕ, (51 * N) / 59450 + 1 ≤ k → k ≤ (54 * N) / 59450 →
      ∃ I : Fin k → ℕ × ℕ,
        (∀ i, (I i).1 < (I i).2) ∧
        (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
        ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1 := by
    intro N hN k hk1 hk2
    obtain ⟨T, hT_sub, hT_div, l, R, hR_bounds, hR_sep, hRT_sep, h_weight, h_low, h_high⟩ := h_scale N hN
    exact packet_switch_interval_extension pellAnchor hA_bounds hA_sep hA_sum N (le_trans hN₀ hN)
      T hT_sub hT_div l R hR_bounds hR_sep hRT_sep h_weight k (le_trans h_low hk1) (le_trans hk2 h_high)
  have h_ind : ∀ d : ℕ, ∀ k : ℕ, (51 * N₀) / 59450 + 1 ≤ k → k ≤ (54 * (N₀ + d)) / 59450 →
      ∃ I : Fin k → ℕ × ℕ,
        (∀ i, (I i).1 < (I i).2) ∧
        (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
        ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1 := by
    intro d
    induction d with
    | zero =>
      intro k hk1 hk2
      exact h_win N₀ (le_refl N₀) k hk1 (by simpa using hk2)
    | succ d ih =>
      intro k hk1 hk2
      by_cases hkd : k ≤ (54 * (N₀ + d)) / 59450
      · exact ih k hk1 hkd
      · apply h_win (N₀ + d + 1) (by omega) k (by omega) (by simpa [Nat.add_assoc] using hk2)
  rw [Filter.eventually_atTop]
  refine ⟨(51 * N₀) / 59450 + 1, fun k hk => ?_⟩
  exact h_ind (59450 * k) k hk (by omega)

end Erdos289
