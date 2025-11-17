import Init.Data.Int.DivMod.Basic
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Init.Data.Int.DivMod.Basic
import Mathlib.Order.Interval.Set.Basic

noncomputable section
open Real

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace PreferComp
  variable {R A B C : Type*}
  variable [Semiring R]
  variable [AddCommMonoid A] [Module R A] [TopologicalSpace A]
  variable [AddCommMonoid B] [Module R B] [TopologicalSpace B]
  variable [AddCommMonoid C] [Module R C] [TopologicalSpace C]
  def mul_eq_comp {f g : A →L[R] A} : g * f = g ∘L f := by rfl
  @[simp] def comp_image S (g : B →L[R] C) (f : A →L[R] B) : ⇑(g ∘L f) '' S = ⇑g '' (⇑f '' S) := by ext p; simp
end PreferComp

open PreferComp

@[simp]
def rot2_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
      | 0, 0 => Real.cos α
      | 0, 1 => -Real.sin α
      | 1, 0 => Real.sin α
      | 1, 1 => Real.cos α

@[simp]
def rot2 : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rot2_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec]

  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;> {
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, rot2_mat, cos_add, sin_add]
      ring_nf
     }

@[simp]
theorem rot2_180 : rot2 π = -1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum]

@[simp]
theorem rot2_neg180 : rot2 (-π) = -1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum]

@[simp]
theorem rot2_360 : rot2 (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum]

@[simp]
theorem rot2_neg360 : rot2 (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum]

@[simp]
theorem rot2_k360 {k : ℤ} : rot2 (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => simp only [Int.cast_add, Int.cast_one, one_mul, right_distrib, AddChar.map_add_eq_mul, h, rot2_360]
  | pred n h =>
      simp only [Int.cast_neg, neg_mul] at h
      simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mul_one, right_distrib, AddChar.map_add_eq_mul, h, rot2_neg360]
@[simp]
def rot3x_mat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun
      | 0, 0 => 1
      | 0, 1 => 0
      | 0, 2 => 0
      | 1, 0 => 0
      | 1, 1 => Real.cos α
      | 1, 2 => -Real.sin α
      | 2, 0 => 0
      | 2, 1 => Real.sin α
      | 2, 2 => Real.cos α

@[simp]
def rot3x : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := (rot3x_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> simp only [rot3x_mat, cos_add, sin_add, neg_add_rev, Fin.zero_eta, Fin.isValue,
      LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum,
      PiLp.ofLp_apply, op_smul_eq_smul, Fin.sum_univ_three, PiLp.toLp_apply, Pi.add_apply,
      Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ContinuousLinearMap.coe_mul, Function.comp_apply] <;> ring

@[simp]
theorem rot3x_360 : rot3x (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3x_neg360 : rot3x (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3x_k360 {k : ℤ} : rot3x (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => simp only [Int.cast_add, Int.cast_one, one_mul, right_distrib, AddChar.map_add_eq_mul, h, rot3x_360]
  | pred n h =>
      simp only [Int.cast_neg, neg_mul] at h
      simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mul_one, right_distrib, AddChar.map_add_eq_mul, h, rot3x_neg360]

@[simp]
def rot3y_mat (α : ℝ) : (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.of fun
      | 0, 0 => Real.cos α
      | 0, 1 => 0
      | 0, 2 => -Real.sin α
      | 1, 0 => 0
      | 1, 1 => 1
      | 1, 2 => 0
      | 2, 0 => Real.sin α
      | 2, 1 => 0
      | 2, 2 => Real.cos α

@[simps]
def rot3y : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := (rot3y_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> simp only [rot3y_mat, cos_add, sin_add, neg_add_rev, Fin.zero_eta, Fin.isValue,
      LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum,
      PiLp.ofLp_apply, op_smul_eq_smul, Fin.sum_univ_three, PiLp.toLp_apply, Pi.add_apply,
      Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ContinuousLinearMap.coe_mul, Function.comp_apply] <;> ring

@[simp]
theorem rot3y_360 : rot3y (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3y_neg360 : rot3y (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3y_k360 {k : ℤ} : rot3y (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => simp only [Int.cast_add, Int.cast_one, one_mul, right_distrib, AddChar.map_add_eq_mul, h, rot3y_360]
  | pred n h =>
      simp only [Int.cast_neg, neg_mul] at h
      simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mul_one, right_distrib, AddChar.map_add_eq_mul, h, rot3y_neg360]

@[simp]
def rot3z_mat (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun
      | 0, 0 => Real.cos α
      | 0, 1 => -Real.sin α
      | 0, 2 => 0
      | 1, 0 => Real.sin α
      | 1, 1 => Real.cos α
      | 1, 2 => 0
      | 2, 0 => 0
      | 2, 1 => 0
      | 2, 2 => 1

@[simps]
def rot3z : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := (rot3z_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> simp only [rot3z_mat, cos_add, sin_add, neg_add_rev, Fin.zero_eta, Fin.isValue,
      LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum,
      PiLp.ofLp_apply, op_smul_eq_smul, Fin.sum_univ_three, PiLp.toLp_apply, Pi.add_apply,
      Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ContinuousLinearMap.coe_mul, Function.comp_apply] <;> ring

@[simp]
theorem rot3z_360 : rot3z (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3z_neg360 : rot3z (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three]

@[simp]
theorem rot3z_k360 {k : ℤ} : rot3z (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => simp only [Int.cast_add, Int.cast_one, one_mul, right_distrib, AddChar.map_add_eq_mul, h, rot3z_360]
  | pred n h =>
      simp only [Int.cast_neg, neg_mul] at h
      simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mul_one, right_distrib, AddChar.map_add_eq_mul, h, rot3z_neg360]

def zhat : ℝ³
  | 0 => 0
  | 1 => 0
  | 2 => 1

@[simp]
def unit3 (θ φ : ℝ) : ℝ³ :=
  rot3z θ ∘ rot3y (-φ) $ zhat

@[simp]
def proj_xy_r90_mat : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun
    | 0, 0 => 0
    | 0, 1 => 1
    | 0, 2 => 0
    | 1, 0 => -1
    | 1, 1 => 0
    | 1, 2 => 0

@[simp]
def proj_xy_r90 : ℝ³ →L[ℝ] ℝ² := proj_xy_r90_mat.toEuclideanLin.toContinuousLinearMap

@[simp]
def flip_y_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => 1
    | 0, 1 => 0
    | 1, 0 => 0
    | 1, 1 => -1

@[simp]
def flip_y : ℝ² →L[ℝ] ℝ² := flip_y_mat.toEuclideanLin.toContinuousLinearMap

@[simp]
def proj_rot (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  proj_xy_r90 ∘L rot3y φ ∘L rot3z (-θ)

theorem rot_proj_rot : rot2 α ∘L proj_rot θ φ = proj_xy_r90 ∘L rot3z α ∘L rot3y φ ∘L rot3z (-θ) := by
  ext v i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

def convex_position (𝕜 V : Type) [PartialOrder 𝕜] [AddCommMonoid 𝕜] [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] (P : Set V) : Prop :=
  ∀ p ∈ P,
    p ∉ convexHull 𝕜 (P \ (Set.singleton p))

def rupert' (P : Set ℝ³) :=
    ∃ (α θ₁ φ₁ θ₂ φ₂ : ℝ),
    (rot2 α ∘L proj_rot θ₁ φ₁) '' P ⊆ (interior $ convexHull ℝ $ proj_rot θ₂ φ₂ '' P)

def C₁ : ℝ³
  | 0 => 152024884 / 259375205
  | 1 => 0
  | 2 => 210152163 / 259375205

def C₂ : ℝ³
  | 0 => 6632738028e-10
  | 1 => 6106948881e-10
  | 2 => 3980949609e-10

def C₃ : ℝ³
  | 0 => 8193990033e-10
  | 1 => 5298215096e-10
  | 2 => 1230614493e-10

def noperthedron_seed : Finset ℝ³ := {C₁, C₂, C₃}

@[simp]
theorem mem_noperthedron_seed (p : ℝ³) :
    p ∈ noperthedron_seed ↔ p = C₁ ∨ p = C₂ ∨ p = C₃ := by
    unfold noperthedron_seed
    grind only [= Finset.mem_insert, = Set.mem_singleton_iff, = Finset.insert_eq_of_mem,
      = Finset.mem_singleton, cases Or]

def noperthedron : Finset ℝ³ :=
    ({1,-1} : Finset ℤ) ×ˢ (Finset.range 15) ×ˢ noperthedron_seed
      |>.image fun (s, (k, p)) => s • rot3z (k * 15⁻¹ * (2 * π)) $ p

def mem_noperthedron' (p : ℝ³) :
    p ∈ noperthedron ↔
    ∃ (s : ℤ) (k : ℕ) (q : ℝ³),
      s ∈ ({1,-1} : Finset ℤ) ∧
      k < 15 ∧
      q ∈ noperthedron_seed ∧
      p = (s • rot3z (k * 15⁻¹ * (2 * π))) q := by
  unfold noperthedron
  simp only [Int.reduceNeg, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨s,k,q,⟨⟨s_in,k_in,q_in⟩,rfl⟩⟩
    use s, k, q
  · rintro ⟨s,k,q,s_in,k_in,q_in,rfl⟩
    use s, k, q

@[simp]
theorem mem_noperthedron (p : ℝ³) :
    p ∈ noperthedron ↔
    ∃ (s : ℤ) (k : ℤ) (q : ℝ³),
      s ∈ ({1,-1} : Finset ℤ) ∧
      q ∈ noperthedron_seed ∧
      p = (s • rot3z (k * 15⁻¹ * (2 * π))) q := by
  rw [mem_noperthedron']
  constructor
  · rintro ⟨s, k, q, ⟨s_in, k_in, q_in, rfl⟩⟩; exists s, k, q
  · rintro ⟨s, k, q, ⟨s_in, q_in, rfl⟩⟩
    let d := k / 15
    let k' := (k % 15).natAbs
    exists s, k', q
    suffices rot3z (k * (1/15) * (2 * π)) = rot3z (k' * (1/15) * (2 * π)) by grind only
    calc
      rot3z (k * (1/15) * (2 * π)) = rot3z ((d * 15 + k % 15 : ℤ) * (1/15) * (2 * π)) := by rw [Int.ediv_mul_add_emod]
      _ = rot3z (((d * 15 : ℤ) + (k % 15 : ℤ)) * (1/15) * (2 * π)) := by simp
      _ = rot3z (d * (2 * π) + (k % 15 : ℤ) * (1/15) * (2 * π)) := by simp [right_distrib]
      _ = rot3z ((k % 15 : ℤ) * (1/15) * (2 * π)) := by simp only [AddChar.map_add_eq_mul, rot3z_k360, one_mul]
      _ = rot3z (k' * (1/15) * (2 * π)) := by rw [( calc (k % 15 : ℤ) = k' := by grind)]; norm_cast


@[simp]
theorem noperthedron_point_symmetric {p : ℝ³} : p ∈ noperthedron → -p ∈ noperthedron := by
    simp only [mem_noperthedron] at *
    rintro ⟨s, k, q, ⟨s_in, q_in, rfl⟩⟩
    exists -s, k, q
    simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton] at s_in
    rcases s_in with rfl|rfl <;> simp only [neg_smul, one_smul, ContinuousLinearMap.neg_apply] <;> grind

theorem lemma7_1 :
  (proj_rot (θ + 2/15*π) φ) '' noperthedron = proj_rot θ φ '' noperthedron := by
  ext p
  simp only [Set.mem_image, SetLike.mem_coe, mem_noperthedron, mem_noperthedron_seed,
    ↓existsAndEq, and_true, and_or_left, or_and_right, exists_or, proj_rot]
  have h (p : ℝ³) (s : ℤ) a b := calc
    (proj_xy_r90 ∘L rot3y φ ∘L rot3z a $ s • rot3z b $ p) = _ := by rfl
    _ = (proj_xy_r90 ∘L rot3y φ ∘L rot3z a ∘L (s • rot3z b)) p := by simp only [ContinuousLinearMap.comp_apply]
    _ = s • (proj_xy_r90 ∘L rot3y φ ∘L rot3z a ∘L rot3z b) p := by simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
    _ = s • (proj_xy_r90 ∘L rot3y φ ∘L (rot3z a ∘L rot3z b)) p := by simp
    _ = s • (proj_xy_r90 ∘L rot3y φ ∘L rot3z (a + b)) p := by simp [AddChar.map_add_eq_mul]
    _ = (proj_xy_r90 ∘L rot3y φ ∘L (s • rot3z (a + b))) p := by simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
  constructor <;> rintro (h|h|h) <;> rcases h with ⟨s, k, ⟨s_in, rfl⟩⟩
  · left
    use s, k-1
    repeat rw [h]
    simp only [Int.cast_sub]
    ring_nf
    trivial
  · right; left
    use s, k-1
    repeat rw [h]
    simp only [Int.cast_sub]
    ring_nf
    trivial
  · right; right
    use s, k-1
    repeat rw [h]
    simp only [Int.cast_sub]
    ring_nf
    trivial
  · left
    use s, k+1
    repeat rw [h]
    simp only [Int.cast_add]
    ring_nf
    trivial
  · right; left
    use s, k+1
    repeat rw [h]
    simp only [Int.cast_add]
    ring_nf
    trivial
  · right; right
    use s, k+1
    repeat rw [h]
    simp only [Int.cast_add]
    ring_nf
    trivial

theorem lemma7_2 :
  (rot2 (α + π) ∘L proj_rot θ φ) '' noperthedron = (rot2 α ∘L proj_rot θ φ) '' noperthedron := by
    ext p
    constructor <;> rintro ⟨q, q_in, rfl⟩ <;> use -q <;> {
      constructor
      apply (noperthedron_point_symmetric q_in)
      simp only [AddChar.map_add_eq_mul, map_neg, rot2_180, ContinuousLinearMap.mul_def, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, neg_neg]
    }

lemma lemma7_3_1 :
  flip_y ∘L proj_rot θ φ = (-proj_rot (θ + π * 15⁻¹) (π - φ)) ∘L rot3z (π * 16 * 15⁻¹) := by
    ext v i
    have h : π * 16 * 15⁻¹ = π * 15⁻¹ + π := by ring
    fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Fin.sum_univ_three, h, right_distrib, cos_add, sin_add, cos_neg, sin_neg]
    · calc
        _ = -(sin θ * v 0) + (cos θ * v 1) := by ring_nf
        _ = (-(sin θ * v 0) + (cos θ * v 1)) * ((sin (π * 15⁻¹))^2 + (cos (π * 15⁻¹))^2) := by simp [Real.sin_sq_add_cos_sq]
        _ = _ := by ring_nf
    · calc
        _ = -(sin φ * v 2) + cos φ * sin θ * v 1 + cos φ * cos θ * v 0 := by ring_nf
        _ = -(sin φ * v 2) + (cos φ * sin θ * v 1 + cos φ * cos θ * v 0) * ((sin (π * 15⁻¹))^2 + (cos (π * 15⁻¹))^2) := by simp [Real.sin_sq_add_cos_sq, add_assoc]
        _ = _ := by ring_nf

lemma lemma7_3_2 :
  (-rot3z (π * 16 * 15⁻¹)) '' noperthedron = noperthedron := by
    ext p
    simp only [Set.mem_image, SetLike.mem_coe, mem_noperthedron]
    constructor
    · rintro ⟨q,⟨s, k, r, s_in, r_in, rfl⟩,rfl⟩
      use -s, (8+k), r
      have h := calc
        (-rot3z (π * 16 * 15⁻¹)) ((s • rot3z (↑k * 15⁻¹ * (2 * π))) r) = _ := by rfl
        _ = (-rot3z (π * 16 * 15⁻¹) ∘L (s • rot3z (↑k * 15⁻¹ * (2 * π)))) r := by rfl
        _ = (-s • (rot3z (16 * 15⁻¹ * π) ∘L rot3z (↑k * 15⁻¹ * (2 * π)))) r := by
          simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, neg_smul]
          ring_nf
        _ = (-s • rot3z (↑(8 + k) * 15⁻¹ * (2 * π))) r := by
          simp only [Int.cast_add, Distrib.right_distrib, AddChar.map_add_eq_mul, mul_eq_comp]
          ring_nf
      rw [h]
      grind
    · rintro ⟨s,k,q,s_in,q_in,rfl⟩
      simp only [↓existsAndEq, and_true]
      use -s, (-8+k), q
      have h := calc
        (-rot3z (π * 16 * 15⁻¹)) ((-s • rot3z (↑(-8 + k) * 15⁻¹ * (2 * π))) q) = _ := by rfl
        _ = (-rot3z (π * 16 * 15⁻¹)) ((-s • rot3z ((-8 + k) * 15⁻¹ * (2 * π))) q) := by simp [Int.cast_add]
        _ = ((-rot3z (π * 16 * 15⁻¹)) ∘L (-s • rot3z ((-8 + k) * 15⁻¹ * (2 * π)))) q := by rfl
        _ = (-s • ((-rot3z (π * 16 * 15⁻¹)) ∘L (rot3z ((-8 + k) * 15⁻¹ * (2 * π))))) q := by
          simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
        _ = (s • ((rot3z (π * 16 * 15⁻¹)) ∘L (rot3z ((-8 + k) * 15⁻¹ * (2 * π))))) q := by
          simp
        _ = (s • (((rot3z (π * 16 * 15⁻¹)) ∘L (rot3z (-8 * 15⁻¹ * (2 * π)))) ∘L rot3z (k * 15⁻¹ * (2 * π)))) q := by
          simp [Distrib.right_distrib, AddChar.map_add_eq_mul, mul_eq_comp]
        _ = (s • (((rot3z (π * 16 * 15⁻¹ + -8 * 15⁻¹ * (2 * π)))) ∘L rot3z (k * 15⁻¹ * (2 * π)))) q := by
          simp [AddChar.map_add_eq_mul]
        _ = (s • (((rot3z 0 ∘L rot3z (k * 15⁻¹ * (2 * π)))))) q := by ring_nf
        _ = (s • rot3z (↑k * 15⁻¹ * (2 * π))) q := by simp
      rw [h]
      grind

theorem lemma7_3 :
  (flip_y ∘L proj_rot θ φ) '' noperthedron = proj_rot (θ + π * 15⁻¹) (π - φ) '' noperthedron := by
    simp only [lemma7_3_1]
    have h : (-proj_rot (θ + π * 15⁻¹) (π - φ)) ∘L (rot3z (π * 16 * 15⁻¹)) = (proj_rot (θ + π * 15⁻¹) (π - φ)) ∘L (-rot3z (π * 16 * 15⁻¹)) := by simp
    simp only [h, comp_image, lemma7_3_2]

theorem lemma9_rot2 :
  ‖rot2 α‖ = 1 := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    simp
    intro x
    simp only [rot2, rot2_mat, AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap',
      Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul,
      Fin.sum_univ_two, Fin.isValue, WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat,
      Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs,
      mul_neg, one_div, one_mul]
    · refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
      · apply add_nonneg <;> apply sq_nonneg
      · apply add_nonneg <;> apply sq_nonneg
      · simp
      · simp only [Fin.isValue, add_sq, mul_neg, even_two, Even.neg_pow]; ring_nf
        calc
          x 0 ^ 2 * cos α ^ 2 + x 0 ^ 2 * sin α ^ 2 + cos α ^ 2 * x 1 ^ 2 + x 1 ^ 2 * sin α ^ 2 = _ := by rfl
          _ = (x 0 ^ 2 + x 1 ^ 2) * (sin α ^ 2 + cos α ^ 2) := by ring
          _ = (x 0 ^ 2 + x 1 ^ 2) := by simp [Real.sin_sq_add_cos_sq]
          _ ≤ _ := by rfl
    · intro N N_nonneg h
      specialize h !₂[1, 0]
      calc
        1 = ‖(rot2 α) !₂[1, 0]‖ := by simp [Matrix.mulVec_eq_sum, PiLp.norm_eq_sum]
        _ ≤ N * ‖!₂[(1 : ℝ), 0]‖ := by assumption
        _ = N := by simp [PiLp.norm_eq_sum]


theorem lemma9_rot3x :
  ‖rot3x α‖ = 1 := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    simp
    intro x
    simp only [rot3x, rot3x_mat, AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap',
      Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul,
      ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.toLp_apply, Finset.sum_apply,
      Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat,
      sq_abs, one_div, one_mul]
    · refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
      · simp only [Fin.sum_univ_three, Fin.isValue, mul_one, mul_zero, add_zero, zero_add, mul_neg]; grind [add_nonneg, sq_nonneg]
      · simp only [Fin.sum_univ_three, Fin.isValue]; grind [add_nonneg, sq_nonneg]
      · simp
      · simp only [Fin.sum_univ_three, Fin.isValue, add_sq, mul_one, mul_zero, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add, mul_neg, even_two,
        Even.neg_pow]; ring_nf
        calc
          x 0 ^ 2 + x 1 ^ 2 * cos α ^ 2 + x 1 ^ 2 * sin α ^ 2 + cos α ^ 2 * x 2 ^ 2 + x 2 ^ 2 * sin α ^ 2 = _ := by rfl
          _ = x 0 ^ 2 + x 1 ^ 2 * (sin α ^ 2 + cos α ^ 2) + x 2 ^ 2 * (sin α ^ 2 + cos α ^ 2) := by simp only [Distrib.left_distrib]; ring
          _ = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by simp
          _ ≤ _ := by rfl
    · intro N N_nonneg h
      specialize h !₂[1, 0, 0]
      calc
        1 = ‖(rot3x α) !₂[1, 0, 0]‖ := by simp [Matrix.mulVec_eq_sum, Fin.sum_univ_three, PiLp.norm_eq_sum]
        _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
        _ = N := by simp [PiLp.norm_eq_sum, Fin.sum_univ_three]

theorem lemma9_rot3y :
  ‖rot3y α‖ = 1 := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    simp
    intro x
    simp only [rot3y, rot3y_mat, AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap',
      Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul,
      ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.toLp_apply, Finset.sum_apply,
      Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat,
      sq_abs, one_div, one_mul]
    · refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
      · simp only [Fin.sum_univ_three, Fin.isValue, mul_zero, add_zero, mul_neg, mul_one, zero_add]; grind [add_nonneg, sq_nonneg]
      · simp only [Fin.sum_univ_three, Fin.isValue]; grind [add_nonneg, sq_nonneg]
      · simp
      · simp only [Fin.sum_univ_three, Fin.isValue, add_sq, mul_one, mul_zero, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add, mul_neg, even_two,
        Even.neg_pow]; ring_nf
        calc
          x 0 ^ 2 * cos α ^ 2 + x 0 ^ 2 * sin α ^ 2 + cos α ^ 2 * x 2 ^ 2 + x 2 ^ 2 * sin α ^ 2 + x 1 ^ 2 = _ := by rfl
          _ = x 0 ^ 2 * (sin α ^ 2 + cos α ^ 2) + x 1 ^ 2 + x 2 ^ 2 * (sin α ^ 2 + cos α ^ 2) := by simp only [Distrib.left_distrib]; ring
          _ = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by simp
          _ ≤ _ := by ring_nf; rfl
    · intro N N_nonneg h
      specialize h !₂[1, 0, 0]
      calc
        1 = ‖(rot3y α) !₂[1, 0, 0]‖ := by simp [Matrix.mulVec_eq_sum, Fin.sum_univ_three, PiLp.norm_eq_sum]
        _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
        _ = N := by simp [PiLp.norm_eq_sum, Fin.sum_univ_three]

theorem lemma9_rot3z :
  ‖rot3z α‖ = 1 := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    simp
    intro x
    simp only [rot3z, rot3z_mat, AddChar.coe_mk, LinearMap.coe_toContinuousLinearMap',
      Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul,
      ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.toLp_apply, Finset.sum_apply,
      Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat,
      sq_abs, one_div, one_mul]
    · refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
      · simp only [Fin.sum_univ_three, Fin.isValue, mul_neg, mul_zero, add_zero, mul_one, zero_add]; grind [add_nonneg, sq_nonneg]
      · simp only [Fin.sum_univ_three, Fin.isValue]; grind [add_nonneg, sq_nonneg]
      · simp
      · simp only [Fin.sum_univ_three, Fin.isValue, add_sq, mul_one, mul_zero, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add, mul_neg, even_two,
        Even.neg_pow]; ring_nf
        calc
          x 0 ^ 2 * cos α ^ 2 + x 0 ^ 2 * sin α ^ 2 + cos α ^ 2 * x 1 ^ 2 + x 1 ^ 2 * sin α ^ 2 + x 2 ^ 2 = _ := by rfl
          _ = x 0 ^ 2 * (sin α ^ 2 + cos α ^ 2) + x 1 ^ 2 * (sin α ^ 2 + cos α ^ 2) + x 2 ^ 2 := by simp only [Distrib.left_distrib]; ring
          _ = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by simp
          _ ≤ _ := by ring_nf; rfl
    · intro N N_nonneg h
      specialize h !₂[1, 0, 0]
      calc
        1 = ‖(rot3z α) !₂[1, 0, 0]‖ := by simp [Matrix.mulVec_eq_sum, Fin.sum_univ_three, PiLp.norm_eq_sum]
        _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
        _ = N := by simp [PiLp.norm_eq_sum, Fin.sum_univ_three]

lemma norm_proj_xy_r90_eq_one :
  ‖proj_xy_r90‖ = 1 := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    simp
    intro x
    simp only [proj_xy_r90, proj_xy_r90_mat, LinearMap.coe_toContinuousLinearMap',
      Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul,
      Fin.sum_univ_three, Fin.isValue, WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat,
      Nat.ofNat_pos, PiLp.norm_eq_sum, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs,
      Fin.sum_univ_two, mul_zero, mul_one, zero_add, add_zero, mul_neg, even_two, Even.neg_pow,
      one_div, one_mul]
    · refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
      · positivity
      · positivity
      · simp
      · ring_nf; simp only [Fin.isValue, le_add_iff_nonneg_right, sq_nonneg]
    · intro N N_nonneg h
      specialize h !₂[1, 0, 0]
      calc
        1 = ‖proj_xy_r90 !₂[1, 0, 0]‖ := by simp [Matrix.mulVec_eq_sum, Fin.sum_univ_three, PiLp.norm_eq_sum]
        _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
        _ = N := by simp [Fin.sum_univ_three, PiLp.norm_eq_sum]

theorem lemma9_proj_rot :
  ‖proj_rot θ φ‖ = 1 := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    simp
    intro x
    · simp only [proj_rot]
      calc
        ‖proj_xy_r90 ∘L rot3y φ ∘L rot3z (-θ) $ x‖ = _ := by rfl
        _ ≤ ‖proj_xy_r90 ∘L rot3y φ ∘L rot3z (-θ)‖ * ‖x‖ := by apply ContinuousLinearMap.le_opNorm
        _ ≤ (‖proj_xy_r90‖ * ‖rot3y φ‖ * ‖rot3z (-θ)‖) * ‖x‖ := by
          apply mul_le_mul_of_nonneg_right
          calc
            ‖proj_xy_r90 ∘L rot3y φ ∘L rot3z (-θ)‖ = _ := by rfl
            _ ≤ ‖proj_xy_r90‖ * ‖rot3y φ ∘L rot3z (-θ)‖ := by apply ContinuousLinearMap.opNorm_comp_le
            _ ≤ ‖proj_xy_r90‖ * ‖rot3y φ‖ * ‖rot3z (-θ)‖ := by
              rw [mul_assoc]
              apply mul_le_mul_of_nonneg_left
              apply ContinuousLinearMap.opNorm_comp_le
              apply norm_nonneg
          apply norm_nonneg
        _ = 1 * ‖x‖ := by grind [norm_proj_xy_r90_eq_one, lemma9_rot3y, lemma9_rot3z]
    · intros N N_nonneg h
      specialize h !₂[-sin θ, cos θ, 0]
      calc
        1 = ((sin θ ^ 2 + cos θ ^ 2) ^ 2) ^ (2 : ℝ)⁻¹ := by simp [Real.sin_sq_add_cos_sq]
        _ = ‖(proj_rot θ φ) !₂[-sin θ, cos θ, 0]‖ := by
          simp only [proj_rot, proj_xy_r90, proj_xy_r90_mat, rot3y_apply, rot3y_mat, rot3z_apply,
            rot3z_mat, cos_neg, sin_neg, neg_neg, ContinuousLinearMap.coe_comp',
            LinearMap.coe_toContinuousLinearMap', Function.comp_apply, Matrix.toEuclideanLin_toLp,
            Matrix.toLin'_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_three,
            Fin.isValue, Matrix.cons_val_zero, neg_smul, Matrix.cons_val_one, Matrix.cons_val,
            zero_smul, add_zero, WithLp.toLp_add, WithLp.toLp_neg, WithLp.toLp_smul, map_add,
            map_neg, map_smul, Matrix.transpose_apply, Matrix.of_apply, smul_add, smul_neg,
            neg_add_rev, one_smul, zero_add, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
            PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul, PiLp.neg_apply,
            norm_eq_abs, rpow_ofNat, sq_abs, Fin.sum_univ_two, mul_one, mul_zero, neg_zero, mul_neg,
            one_div]
          ring_nf
        _ ≤ N * ‖!₂[-sin θ, cos θ, 0]‖ := by assumption
        _ = N := by simp [Fin.sum_univ_three, PiLp.norm_eq_sum]

theorem dist_rot2_apply :
  ‖(rot2 α - rot2 α') v‖ = 2 * |sin ((α - α') / 2)| * ‖v‖ := by
    simp only [rot2, rot2_mat, AddChar.coe_mk, ContinuousLinearMap.coe_sub',
      LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul, Fin.sum_univ_two, Fin.isValue,
      WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, Matrix.transpose_apply,
      Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_neg, one_div]
    calc
      ((v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
        (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ = _ := by rfl
      _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2)) ^ (2 : ℝ)⁻¹ := by
        have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
        refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
        calc
          (v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
            (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2 = _ := by rfl
          _ = (v 0 * (cos α - cos α') - v 1 * (sin α - sin α')) ^ 2 + (v 0 * (sin α - sin α') + v 1 * (cos α - cos α')) ^ 2 := by ring_nf
          _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 * ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
            simp only [Fin.isValue, cos_sub_cos, neg_mul, mul_neg, sin_sub_sin, sq]
            ring_nf
          _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 := by simp [sin_sq_add_cos_sq]
          _ = (2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
      _ = 2 * |sin ((α - α') / 2)| * (v 0 ^ 2 + v 1 ^ 2) ^ (2 : ℝ)⁻¹ := by
        rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
        simp only [Fin.isValue, sqrt_sq_eq_abs, abs_mul, Nat.abs_ofNat, rpow_one, one_div]
        all_goals positivity

theorem dist_rot3x_apply :
  ‖(rot3x α - rot3x α') v‖ = 2 * |sin ((α - α') / 2)| * ‖!₂[v 1, v 2]‖ := by
    simp only [rot3x, rot3x_mat, AddChar.coe_mk, ContinuousLinearMap.coe_sub',
      LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue,
      WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, Matrix.transpose_apply,
      Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_one, mul_zero, add_zero,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_neg, one_div,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc
      ((v 1 * cos α + -(v 2 * sin α) - (v 1 * cos α' + -(v 2 * sin α'))) ^ 2 +
        (v 1 * sin α + v 2 * cos α - (v 1 * sin α' + v 2 * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ = _ := by rfl
      _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v 1 ^ 2 + v 2 ^ 2)) ^ (2 : ℝ)⁻¹ := by
        have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
        refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
        calc
          (v 1 * cos α + -(v 2 * sin α) - (v 1 * cos α' + -(v 2 * sin α'))) ^ 2 +
            (v 1 * sin α + v 2 * cos α - (v 1 * sin α' + v 2 * cos α')) ^ 2 = _ := by rfl
          _ = (v 1 * (cos α - cos α') - v 2 * (sin α - sin α')) ^ 2 + (v 1 * (sin α - sin α') + v 2 * (cos α - cos α')) ^ 2 := by ring_nf
          _ = 4 * (v 1 ^ 2 + v 2 ^ 2) * (sin ((α - α') / 2)) ^ 2 * ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
            simp [sin_sub_sin, cos_sub_cos, sq]
            ring_nf
          _ = 4 * (v 1 ^ 2 + v 2 ^ 2) * (sin ((α - α') / 2)) ^ 2 := by simp [sin_sq_add_cos_sq]
          _ = (2 * sin ((α - α') / 2)) ^ 2 * (v 1 ^ 2 + v 2 ^ 2) := by ring
      _ = 2 * |sin ((α - α') / 2)| * (v 1 ^ 2 + v 2 ^ 2) ^ (2 : ℝ)⁻¹ := by
        rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
        simp [sqrt_sq_eq_abs]
        all_goals positivity

theorem dist_rot3y_apply :
  ‖(rot3y α - rot3y α') v‖ = 2 * |sin ((α - α') / 2)| * ‖!₂[v 0, v 2]‖ := by
    simp only [rot3y, rot3y_mat, AddChar.coe_mk, ContinuousLinearMap.coe_sub',
      LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue,
      WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, Matrix.transpose_apply,
      Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_one, mul_zero, add_zero,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_neg, one_div,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc
      ((v 0 * cos α + -(v 2 * sin α) - (v 0 * cos α' + -(v 2 * sin α'))) ^ 2 +
        (v 0 * sin α + v 2 * cos α - (v 0 * sin α' + v 2 * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ = _ := by rfl
      _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 2 ^ 2)) ^ (2 : ℝ)⁻¹ := by
        have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
        refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
        calc
          (v 0 * cos α + -(v 2 * sin α) - (v 0 * cos α' + -(v 2 * sin α'))) ^ 2 +
            (v 0 * sin α + v 2 * cos α - (v 0 * sin α' + v 2 * cos α')) ^ 2 = _ := by rfl
          _ = (v 0 * (cos α - cos α') - v 2 * (sin α - sin α')) ^ 2 + (v 0 * (sin α - sin α') + v 2 * (cos α - cos α')) ^ 2 := by ring_nf
          _ = 4 * (v 0 ^ 2 + v 2 ^ 2) * (sin ((α - α') / 2)) ^ 2 * ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
            simp [sin_sub_sin, cos_sub_cos, sq]
            ring_nf
          _ = 4 * (v 0 ^ 2 + v 2 ^ 2) * (sin ((α - α') / 2)) ^ 2 := by simp [sin_sq_add_cos_sq]
          _ = (2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 2 ^ 2) := by ring
      _ = 2 * |sin ((α - α') / 2)| * (v 0 ^ 2 + v 2 ^ 2) ^ (2 : ℝ)⁻¹ := by
        rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
        simp [sqrt_sq_eq_abs]
        all_goals positivity

theorem dist_rot3z_apply :
  ‖(rot3z α - rot3z α') v‖ = 2 * |sin ((α - α') / 2)| * ‖!₂[v 0, v 1]‖ := by
    simp only [rot3z, rot3z_mat, AddChar.coe_mk, ContinuousLinearMap.coe_sub',
      LinearMap.coe_toContinuousLinearMap', Pi.sub_apply, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_eq_sum, PiLp.ofLp_apply, op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue,
      WithLp.toLp_add, WithLp.toLp_smul, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, Matrix.transpose_apply,
      Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_one, mul_zero, add_zero,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_neg, one_div,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc
      ((v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
        (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2) ^ (2 : ℝ)⁻¹ = _ := by rfl
      _ = ((2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2)) ^ (2 : ℝ)⁻¹ := by
        have one_neg_cos_nonneg : 0 ≤ 1 - cos (α - α') := by simp [cos_le_one]
        refine (rpow_left_inj ?_ ?_ ?_).mpr ?_ <;> try positivity
        calc
          (v 0 * cos α + -(v 1 * sin α) - (v 0 * cos α' + -(v 1 * sin α'))) ^ 2 +
            (v 0 * sin α + v 1 * cos α - (v 0 * sin α' + v 1 * cos α')) ^ 2 = _ := by rfl
          _ = (v 0 * (cos α - cos α') - v 1 * (sin α - sin α')) ^ 2 + (v 0 * (sin α - sin α') + v 1 * (cos α - cos α')) ^ 2 := by ring_nf
          _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 * ((sin ((α + α') / 2)) ^ 2 + (cos ((α + α') / 2)) ^ 2) := by
            simp [sin_sub_sin, cos_sub_cos, sq]
            ring_nf
          _ = 4 * (v 0 ^ 2 + v 1 ^ 2) * (sin ((α - α') / 2)) ^ 2 := by simp [sin_sq_add_cos_sq]
          _ = (2 * sin ((α - α') / 2)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
      _ = 2 * |sin ((α - α') / 2)| * (v 0 ^ 2 + v 1 ^ 2) ^ (2 : ℝ)⁻¹ := by
        rw [mul_rpow, inv_eq_one_div, rpow_div_two_eq_sqrt]
        simp [sqrt_sq_eq_abs]
        all_goals positivity

theorem dist_rot2 :
  ‖rot2 α - rot2 α'‖ = 2 * |sin ((α - α') / 2)| := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    positivity
    · intro v
      rw [dist_rot2_apply]
    · intro N N_nonneg h
      specialize h !₂[1, 0]
      have norm_xhat_eq_one : ‖!₂[(1 : ℝ), 0]‖ = 1 := by simp [PiLp.norm_eq_sum, Fin.sum_univ_two]
      calc
        2 * |sin ((α - α') / 2)| = _ := by rfl
        _ = ‖(rot2 α - rot2 α') !₂[(1 : ℝ), 0]‖ := by simp only [dist_rot2_apply, norm_xhat_eq_one, mul_one]
        _ ≤ N * ‖!₂[(1 : ℝ), 0]‖ := by assumption
        _ = N := by simp [norm_xhat_eq_one]

theorem dist_rot3x :
  ‖rot3x α - rot3x α'‖ = 2 * |sin ((α - α') / 2)| := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    positivity
    · intro v
      rw [dist_rot3x_apply]
      by_cases h : |sin ((α - α') / 2)| = 0
      · rw [h]; simp
      · field_simp
        simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
        apply rpow_le_rpow <;> norm_num <;> positivity
    · intro N N_nonneg h
      specialize h !₂[0, 1, 0]
      have norm_xhat_eq_one : ‖!₂[(1 : ℝ), 0]‖ = 1 := by simp [PiLp.norm_eq_sum]
      calc
        2 * |sin ((α - α') / 2)| = _ := by rfl
        _ = ‖(rot3x α - rot3x α') !₂[0, (1 : ℝ), 0]‖ := by
          simp only [dist_rot3x_apply]
          simp [norm_xhat_eq_one, mul_one]
        _ ≤ N * ‖!₂[0, (1 : ℝ), 0]‖ := by assumption
        _ = N := by simp [PiLp.norm_eq_sum, Fin.sum_univ_three]

theorem dist_rot3y :
  ‖rot3y α - rot3y α'‖ = 2 * |sin ((α - α') / 2)| := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    positivity
    · intro v
      rw [dist_rot3y_apply]
      by_cases h : |sin ((α - α') / 2)| = 0
      · rw [h]; simp
      · field_simp
        simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
        apply rpow_le_rpow <;> norm_num <;> positivity
    · intro N N_nonneg h
      specialize h !₂[1, 0, 0]
      have norm_xhat_eq_one : ‖!₂[(1 : ℝ), 0]‖ = 1 := by simp [PiLp.norm_eq_sum]
      calc
        2 * |sin ((α - α') / 2)| = _ := by rfl
        _ = ‖(rot3y α - rot3y α') !₂[(1 : ℝ), 0, 0]‖ := by
          simp only [dist_rot3y_apply]
          simp [norm_xhat_eq_one, mul_one]
        _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
        _ = N := by simp [PiLp.norm_eq_sum, Fin.sum_univ_three]

theorem dist_rot3z :
  ‖rot3z α - rot3z α'‖ = 2 * |sin ((α - α') / 2)| := by
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    positivity
    · intro v
      rw [dist_rot3z_apply]
      by_cases h : |sin ((α - α') / 2)| = 0
      · rw [h]; simp
      · field_simp
        simp [PiLp.norm_eq_sum, Fin.sum_univ_three]
        apply rpow_le_rpow <;> norm_num <;> positivity
    · intro N N_nonneg h
      specialize h !₂[1, 0, 0]
      have norm_xhat_eq_one : ‖!₂[(1 : ℝ), 0]‖ = 1 := by simp [PiLp.norm_eq_sum]
      calc
        2 * |sin ((α - α') / 2)| = _ := by rfl
        _ = ‖(rot3z α - rot3z α') !₂[(1 : ℝ), 0, 0]‖ := by
          simp only [dist_rot3z_apply]
          norm_num
          simp only [norm_xhat_eq_one, mul_one]
        _ ≤ N * ‖!₂[(1 : ℝ), 0, 0]‖ := by assumption
        _ = N := by simp [PiLp.norm_eq_sum, Fin.sum_univ_three]

theorem dist_rot3x_eq_dist_rot {α α' : ℝ} :
  ‖rot3x α - rot3x α'‖ = ‖rot2 α - rot2 α'‖ := by simp only [dist_rot3x, dist_rot2]

theorem dist_rot3y_eq_dist_rot {α α' : ℝ} :
  ‖rot3y α - rot3y α'‖ = ‖rot2 α - rot2 α'‖ := by simp only [dist_rot3y, dist_rot2]

theorem dist_rot3z_eq_dist_rot {α α' : ℝ} :
  ‖rot3z α - rot3z α'‖ = ‖rot2 α - rot2 α'‖ := by simp only [dist_rot3z, dist_rot2]

lemma two_mul_abs_sin_half_le : 2 * |sin (α / 2)| ≤ |α| := by
  have h : |sin (α / 2)| ≤ |α / 2| := abs_sin_le_abs
  calc
    2 * |sin (α / 2)| = _ := by rfl
    _ ≤ 2 * |α / 2| := by simp [h]
    _ = 2 * (|α| / 2) := by simp [abs_div]
    _ = |α| := by field

theorem dist_rot2_le_dist : ‖rot2 α - rot2 α'‖ ≤ ‖α - α'‖ := by
  calc
    ‖rot2 α - rot2 α'‖ = _ := by rfl
    _ = 2 * |sin ((α - α') / 2)| := by apply dist_rot2
    _ ≤ |α - α'| := by apply two_mul_abs_sin_half_le

lemma one_add_cos_eq : 1 + cos α = 2 * cos (α / 2) ^ 2 := by rw [cos_sq]; field_simp

lemma lemma11_1_1 : cos (√(α ^ 2 + β ^ 2) / 2) ^ 2 = cos (√((-α) ^ 2 + β ^ 2) / 2) ^ 2 := by simp
lemma lemma11_1_2 : cos (√(α ^ 2 + β ^ 2) / 2) ^ 2 = cos (√(α ^ 2 + (-β) ^ 2) / 2) ^ 2 := by simp
lemma lemma11_1_3 : cos (α / 2) ^ 2 * cos (β / 2) ^ 2 = cos ((-α) / 2) ^ 2 * cos (β / 2) ^ 2 := by simp only [neg_div, cos_neg]
lemma lemma11_1_4 : cos (α / 2) ^ 2 * cos (β / 2) ^ 2 = cos (α / 2) ^ 2 * cos ((-β) / 2) ^ 2 := by simp only [neg_div, cos_neg]

def sin_sub_mul_cos (x : ℝ) : ℝ := sin x - x * cos x

lemma sin_sub_mul_cos_monotone_on : MonotoneOn sin_sub_mul_cos (Set.Icc 0 π) := by
  apply monotoneOn_of_deriv_nonneg
  apply convex_Icc
  apply Continuous.continuousOn
  unfold sin_sub_mul_cos
  continuity
  unfold sin_sub_mul_cos
  simp only [interior_Icc]
  apply DifferentiableOn.sub
  apply Differentiable.differentiableOn
  simp
  apply DifferentiableOn.mul
  apply Differentiable.differentiableOn
  simp
  apply Differentiable.differentiableOn
  simp
  simp only [interior_Icc]
  intros x x_in
  unfold sin_sub_mul_cos
  simp only [differentiableAt_sin, differentiableAt_fun_id, differentiableAt_cos,
    DifferentiableAt.fun_mul, deriv_fun_sub, Real.deriv_sin, deriv_fun_mul, deriv_id'', one_mul,
    deriv_cos', mul_neg, sub_add_cancel_left, neg_neg]
  have := sin_pos_of_mem_Ioo x_in
  simp at x_in
  rcases x_in with ⟨x_pos,x_lt⟩
  apply mul_nonneg <;> linarith

lemma sin_sub_mul_cos_nonneg : x ∈ Set.Icc 0 π → 0 ≤ sin_sub_mul_cos x := by
  simp only [Set.mem_Icc, and_imp]
  intros x_nonneg x_le
  calc
    0 = sin_sub_mul_cos 0 := by simp [sin_sub_mul_cos]
    _ ≤ sin_sub_mul_cos x := by
      apply sin_sub_mul_cos_monotone_on <;> (try simp only [Set.mem_Icc, le_refl, true_and]) <;> grind

lemma convexOn_cos_sqrt : ConvexOn ℝ (Set.Icc 0 (π^2)) (cos ∘ sqrt) := by
  have cos_sqrt_deriv : ∀ x ∈ Set.Ioo 0 (π ^ 2), deriv (cos ∘ sqrt) x = -sin √x / (2 * √x) := by
    simp only [Set.mem_Ioo, and_imp]
    intros x x_pos x_lt
    rw [deriv_comp, deriv_cos', deriv_sqrt, deriv_id'']
    · field_simp
    · simp
    · linarith
    · simp
    · apply DifferentiableAt.sqrt
      simp
      linarith
  apply convexOn_of_deriv2_nonneg
  · apply convex_Icc
  · refine ContinuousOn.comp (t:=Set.univ) ?_ ?_ ?_
    · continuity
    · apply Continuous.continuousOn
      continuity
    · apply Set.mapsTo_iff_subset_preimage.mpr
      simp
  · refine DifferentiableOn.comp (t:=Set.univ) ?_ ?_ ?_
    · apply Differentiable.differentiableOn
      simp
    · simp only [interior_Icc]
      apply DifferentiableOn.sqrt
      · apply Differentiable.differentiableOn
        simp
      · grind
    · apply Set.mapsTo_iff_subset_preimage.mpr
      simp
  · simp only [interior_Icc]
    apply DifferentiableOn.congr (f := (-((sin ·) / (2 * ·)) ∘ sqrt))
    · simp only [differentiableOn_neg_iff]
      apply DifferentiableOn.comp (t:=Set.Ioi 0)
      · apply DifferentiableOn.div
        · apply Differentiable.differentiableOn
          simp
        · apply Differentiable.differentiableOn
          apply Differentiable.mul
          simp
          simp
        · grind
      · apply DifferentiableOn.sqrt
        apply Differentiable.differentiableOn
        · simp
        · grind
      · apply Set.mapsTo_iff_subset_preimage.mpr
        simp only [Set.subset_def, Set.mem_Ioo, Set.mem_preimage, Set.mem_Ioi, sqrt_pos, and_imp]
        grind
    · intros x x_in
      simp only [Pi.neg_apply, Function.comp_apply, Pi.div_apply]
      grind
  · simp only [interior_Icc, Set.mem_Ioo, Function.iterate_succ, Function.iterate_zero, Function.id_def,
    Function.comp_apply, and_imp]
    intro x x_pos x_lt
    rw [(Set.EqOn.deriv (_ : Set.EqOn (deriv (cos ∘ sqrt)) (fun y => -sin √y / (2 * √y)) (Set.Ioo 0 (π^2))) (by simp [Ioo_eq_ball] : IsOpen (Set.Ioo 0 (π^2))))]
    rw [deriv_fun_div]
    simp only [deriv.fun_neg', neg_mul, deriv_const_mul_field',
      sub_neg_eq_add]
    conv in (fun y => sin √y) =>
      change (sin ∘ sqrt)
    rw [deriv_comp, deriv_sqrt, _root_.deriv_sin, deriv_id'']
    simp only [mul_one, one_div, mul_inv_rev]
    field_simp; ring_nf
    rw [add_comm]
    apply sin_sub_mul_cos_nonneg
    simp only [Set.mem_Icc, sqrt_nonneg, sqrt_le_iff, true_and]
    constructor
    exact pi_nonneg
    linarith
    · simp
    · simp
    · linarith
    · simp
    · apply DifferentiableAt.sqrt
      simp
      linarith
    · simp only [differentiableAt_fun_neg_iff]
      apply DifferentiableAt.fun_comp'
      simp
      apply DifferentiableAt.sqrt
      simp
      linarith
    · apply DifferentiableAt.const_mul
      apply DifferentiableAt.sqrt
      simp
      linarith
    · have : 0 < √x := sqrt_pos.mpr x_pos
      linarith
    · grind
    · intros x; apply cos_sqrt_deriv

theorem lemma11_1 : |α| ≤ 2 → |β| ≤ 2 → 2 * (1 + cos √(α^2 + β^2)) ≤ (1 + cos α) * (1 + cos β) := by
  repeat rw [one_add_cos_eq]
  field_simp
  suffices ∀ α β, 0 ≤ α → α ≤ 2 → 0 ≤ β → β ≤ 2 → cos (√(α ^ 2 + β ^ 2) / 2) ^ 2 ≤ cos (α / 2) ^ 2 * cos (β / 2) ^ 2 by
    simp [abs_le]
    intro le_α α_le le_β β_le
    by_cases α_sign : 0 ≤ α <;> by_cases β_sign : 0 ≤ β
    · apply this <;> linarith
    · rw [lemma11_1_2, lemma11_1_4]
      apply this <;> linarith
    · rw [lemma11_1_1, lemma11_1_3]
      apply this <;> linarith
    · rw [lemma11_1_1, lemma11_1_2, lemma11_1_3, lemma11_1_4]
      apply this <;> linarith
  intros α β α_nonneg α_le β_nonneg β_le
  rw [(
    calc
      √(α ^ 2 + β ^ 2) / 2 = _ := by rfl
      _ = √((α / 2) ^ 2 + (β / 2) ^ 2) := by field_simp; simp; field_simp
  )]
  generalize hα : α / 2 = x, hβ : β / 2 = y
  rw [(
    calc
      cos x ^ 2 * cos y ^ 2 = (cos x * cos y) ^ 2 := by simp [sq]; ring
  )]
  apply sq_le_sq.mpr
  repeat rw [abs_of_nonneg]
  suffices 2 * cos √(x ^ 2 + y ^ 2) ≤ 2 * cos x * cos y by field_simp at this; assumption
  rw [two_mul_cos_mul_cos]
  let f := cos ∘ sqrt
  calc
    2 * cos √(x ^ 2 + y ^ 2) = _ := by rfl
    _ = 2 * f (x ^ 2 + y ^ 2) := by rfl
    _ = 2 * f (1/2 * (x - y)^2 + 1/2 * (x + y)^2) := by ring_nf
    _ ≤ 2 * (1/2 * f ((x - y)^2) + 1/2 * f ((x + y)^2)) := by
      subst hα hβ
      simp only [mul_le_mul_iff_right₀, Nat.ofNat_pos]
      apply convexOn_cos_sqrt.2
      · simp
        constructor
        · positivity
        · apply sq_le_sq.mpr
          field_simp
          simp only [abs_div, Nat.abs_ofNat]
          field_simp
          apply le_of_lt
          calc
            |α - β| = _ := by rfl
            _ ≤ |α| + |β| := by apply abs_sub
            _ ≤ 2 * 3 := by (repeat rw [abs_of_nonneg]) <;> linarith
            _ < 2 * π := by simp [pi_gt_three]
            _ = 2 * |π| := by rw [abs_of_nonneg] ; positivity
      · simp
        constructor
        · positivity
        · apply sq_le_sq.mpr
          repeat rw [abs_of_nonneg]
          field_simp
          apply le_of_lt
          calc
            α + β = _ := by rfl
            _ ≤ 2 * 3 := by linarith
            _ < 2 * π := by simp [pi_gt_three]
          · positivity
          · positivity
      · positivity
      · positivity
      · ring
    _ = f ((x - y)^2) + f ((x + y)^2) := by field_simp
    _ = cos √((x - y)^2) + cos √((x + y)^2) := by simp [f]
    _ = cos |x - y| + cos |x + y| := by simp [sqrt_sq_eq_abs]
    _ = cos (x - y) + cos (x + y) := by simp
  · subst hα hβ
    have : 3 < π := pi_gt_three
    apply mul_nonneg <;> {
      apply cos_nonneg_of_mem_Icc
      constructor
      · linarith
      · linarith
    }
  · have : 3 < π := pi_gt_three
    apply cos_nonneg_of_mem_Icc
    constructor
    · calc
        -(π/2) ≤ 0 := by linarith
        _ = √0 := by simp
        _ ≤ √(x ^ 2 + y ^ 2) := by
          apply sqrt_monotone
          positivity
    · subst hα hβ
      field_simp
      rw [sqrt_div, sqrt_sq]
      field_simp
      apply le_of_lt
      calc
        √(α^2 + β^2) ≤ √(2^2 + 2^2) := by
          apply sqrt_monotone
          apply add_le_add <;> apply sq_le_sq.mpr <;> simpa [abs_of_nonneg, α_nonneg, β_nonneg]
        _ = √8 := by ring_nf
        _ ≤ 3 := by simp only [sqrt_le_iff, Nat.ofNat_nonneg, true_and]; linarith
        _ < π := by assumption
      linarith
      positivity

-- requires matrix form of Euler's rotation theorem
-- which in turn requires Schur decomposition
lemma rot3x_rot3y_orth_equiv_rotz : ∃ (u : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (γ : ℝ),
  γ ∈ Set.Ico (-π) π ∧ rot3x α ∘L rot3y β = u ∘L rot3z γ ∘L u.symm := by sorry

abbrev tr := LinearMap.trace ℝ ℝ³
abbrev tr' := LinearMap.trace ℝ (Fin 3 → ℝ)

lemma tr_rot3x_rot3y : tr (rot3x α ∘L rot3y β) = cos α + cos β + cos α * cos β :=
  calc tr (rot3x α ∘L rot3y β)
  _ = tr' ((rot3x_mat α).toLin' ∘ₗ (rot3y_mat β).toLin') := by rfl
  _ = tr' ((rot3x_mat α * rot3y_mat β).toLin') := by simp
  _ = Matrix.trace (rot3x_mat α * rot3y_mat β) := by rw [Matrix.trace_toLin'_eq]
  _ = cos α + cos β + cos α * cos β := by
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

lemma tr_rot3z : tr (rot3z α) = 1 + 2 * cos α :=
  calc tr (rot3z α)
  _ = tr' ((rot3z_mat α).toLin') := by rfl
  _ = Matrix.trace (rot3z_mat α) := by rw [Matrix.trace_toLin'_eq]
  _ = 1 + 2 * cos α := by
    simp [Matrix.trace, Fin.sum_univ_three]
    ring_nf

theorem lemma12_1 :
  |α| ≤ 2 → |β| ≤ 2 → ‖rot3x α ∘L rot3y β - 1‖ ≤ √(α^2 + β^2) := by
  intros α_le β_le
  obtain ⟨u, γ, γ_in, rx_ry_eq⟩ := rot3x_rot3y_orth_equiv_rotz (α:=α) (β:=β)
  rw [rx_ry_eq]
  have h : |γ| ≤ √(α^2 + β^2) := by
    suffices cos √(α^2 + β^2) ≤ cos γ by
      apply le_of_not_gt
      intro h
      apply strictAntiOn_cos at h
      · by_cases γ_sign : 0 ≤ γ
        · rw [abs_of_nonneg] at h <;> linarith
        · rw [abs_of_neg, cos_neg] at h <;> linarith
      · simp only [Set.mem_Ico, Set.mem_Icc, sqrt_nonneg, true_and] at ⊢ γ_in
        apply sqrt_le_iff.mpr
        constructor
        · positivity
        · rw [←(sq_abs α), ←(sq_abs β)]
          grw [α_le, β_le]
          calc
          _ ≤ 3^2 := by norm_num
          _ ≤ π^2 := by simp only [sq_le_sq, Nat.abs_ofNat, pi_nonneg, abs_of_nonneg,
            pi_gt_three, le_of_lt]
      · simp only [Set.mem_Icc, abs_nonneg, abs_le, true_and]
        obtain ⟨le_γ, γ_lt⟩ := γ_in
        constructor <;> linarith

    suffices 2 * (1 + cos √(α^2 + β^2)) ≤ 2 * (1 + cos γ) by grind
    calc 2 * (1 + cos √(α^2 + β^2))
    _ ≤ (1 + cos α) * (1 + cos β) := by
      apply lemma11_1 <;> assumption
    _ = (cos α + cos β + cos α * cos β) + 1 := by ring_nf
    _ = tr (rot3x α ∘L rot3y β) + 1 := by rw [←tr_rot3x_rot3y]
    _ = tr (u ∘L rot3z γ ∘L u.symm : ℝ³ →L[ℝ] ℝ³) + 1 := by rw [rx_ry_eq]
    _ = tr (u.conj (rot3z γ)) + 1 := by rfl
    _ = tr (rot3z γ) + 1 := by rw [LinearMap.trace_conj']
    _ = 2 + 2 * cos γ := by rw [tr_rot3z]; ring_nf
    _ = 2 * (1 + cos γ) := by ring_nf

  sorry
