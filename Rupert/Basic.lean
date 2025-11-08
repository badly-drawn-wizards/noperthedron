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
  @[scoped simp] def mul_eq_comp {f g : A →L[R] A} : g * f = g ∘L f := by rfl
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
@[reducible]
def rot2 : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := {
    toFun := (rot2_mat α).toLin'
    map_add' := by apply LinearMap.map_add
    map_smul' := by apply LinearMap.map_smul
  }
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.mulVec]

  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;> simp [Matrix.mulVec] <;> simp [Real.sin_add, Real.cos_add] <;> ring

@[simp]
theorem rot2_180 : rot2 π = -1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec]

@[simp]
theorem rot2_neg180 : rot2 (-π) = -1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec]

@[simp]
theorem rot2_360 : rot2 (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec]

@[simp]
theorem rot2_neg360 : rot2 (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec]

@[simp]
theorem rot2_k360 {k : ℤ} : rot2 (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul]

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

@[reducible]
def rot3x : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := {
    toFun := (rot3x_mat α).toLin'
    map_add' := by apply LinearMap.map_add
    map_smul' := by apply LinearMap.map_smul
  }
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Real.sin_add, Real.cos_add] <;> ring

@[simp]
theorem rot3x_360 : rot3x (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp]
theorem rot3x_neg360 : rot3x (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp]
theorem rot3x_k360 {k : ℤ} : rot3x (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul]

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

@[reducible]
def rot3y : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := {
    toFun := (rot3y_mat α).toLin'
    map_add' := by apply LinearMap.map_add
    map_smul' := by apply LinearMap.map_smul
  }
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Real.sin_add, Real.cos_add] <;> ring

@[simp]
theorem rot3y_360 : rot3y (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp]
theorem rot3y_neg360 : rot3y (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp]
theorem rot3y_k360 {k : ℤ} : rot3y (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul]

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

@[reducible]
def rot3z : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := {
    toFun := (rot3z_mat α).toLin'
    map_add' := by apply LinearMap.map_add
    map_smul' := by apply LinearMap.map_smul
  }
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Real.sin_add, Real.cos_add] <;> ring

@[simp]
theorem rot3z_360 : rot3z (2 * π) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp]
theorem rot3z_neg360 : rot3z (-(2 * π)) = 1 := by
  ext v i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp]
theorem rot3z_k360 {k : ℤ} : rot3z (k * (2 * π)) = 1 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul]

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

@[reducible]
def proj_xy_r90 : ℝ³ →L[ℝ] ℝ² where
  toFun := proj_xy_r90_mat.toLin'
  map_add' := by apply LinearMap.map_add
  map_smul' := by apply LinearMap.map_smul

@[simp]
def flip_y_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => 1
    | 0, 1 => 0
    | 1, 0 => 0
    | 1, 1 => -1

@[reducible]
def flip_y : ℝ² →L[ℝ] ℝ² where
  toFun := flip_y_mat.toLin'
  map_add' := by apply LinearMap.map_add
  map_smul' := by apply LinearMap.map_smul

@[simp]
def proj_rot (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  proj_xy_r90 ∘L rot3y φ ∘L rot3z (-θ)

theorem rot_proj_rot : rot2 α ∘L proj_rot θ φ = proj_xy_r90 ∘L rot3z α ∘L rot3y φ ∘L rot3z (-θ) := by
  ext v i
  fin_cases i <;> simp [Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

def convex_position (𝕜 V : Type) [PartialOrder 𝕜] [AddCommMonoid 𝕜] [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] (P : Set V) : Prop :=
  ∀ p ∈ P,
    p ∉ convexHull 𝕜 (P \ (Set.singleton p))

def rupert' (P : Set ℝ³) :=
    ∃ (α θ₁ φ₁ θ₂ φ₂ : ℝ), ∀ p ∈ P,
    (rot2 α ∘L proj_rot θ₁ φ₁) p ∈ (interior $ convexHull ℝ $ proj_rot θ₂ φ₂ '' P)

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
      _ = rot3z ((k % 15 : ℤ) * (1/15) * (2 * π)) := by simp [AddChar.map_add_eq_mul]
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
      simp [AddChar.map_add_eq_mul, map_neg]
    }

lemma lemma7_3_1 :
  flip_y ∘L proj_rot θ φ = (-proj_rot (θ + π * 15⁻¹) (π - φ)) ∘L rot3z (π * 16 * 15⁻¹) := by
    ext v i
    have h : π * 16 * 15⁻¹ = π * 15⁻¹ + π := by ring
    fin_cases i <;> simp only [proj_rot, AddChar.coe_mk, rot3y_mat, rot3z_mat, cos_neg, sin_neg,
      neg_neg, Fin.zero_eta, Fin.isValue, ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.coe_mk', flip_y_mat, LinearMap.coe_mk, AddHom.coe_mk, proj_xy_r90_mat,
      Function.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three, zero_mul, add_zero, neg_mul, one_mul,
      zero_add, mul_zero, neg_zero, mul_neg, mul_one, Fin.sum_univ_two, cos_pi_sub, sin_pi_sub,
      neg_add_rev, cos_add, sin_add, h, cos_pi, sin_pi, sub_zero, ContinuousLinearMap.neg_apply,
      PiLp.neg_apply] <;> ring_nf
    · calc
        -(sin θ * v 0) + (cos θ * v 1) = _ := by rfl
        _ = (-(sin θ * v 0) + (cos θ * v 1)) * ((sin (π * 15⁻¹))^2 + (cos (π * 15⁻¹))^2) := by simp [Real.sin_sq_add_cos_sq]
        _ = _ := by ring_nf
    · calc
        -(sin φ * v 2) + cos φ * sin θ * v 1 + cos φ * cos θ * v 0 = _ := by rfl
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
    simp only [AddChar.coe_mk, rot2_mat, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.toLin'_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_two,
      Fin.isValue, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, Pi.add_apply,
      Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat,
      sq_abs, mul_neg, one_div, one_mul]
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
    simp only [AddChar.coe_mk, rot3x_mat, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.toLin'_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul,
      ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, Finset.sum_apply, Pi.smul_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs,
      one_div, one_mul]
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
    simp only [AddChar.coe_mk, rot3y_mat, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.toLin'_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul,
      ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, Finset.sum_apply, Pi.smul_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs,
      one_div, one_mul]
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
    simp only [AddChar.coe_mk, rot3z_mat, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.toLin'_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul,
      ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, Finset.sum_apply, Pi.smul_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs,
      one_div, one_mul]
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
    simp only [ContinuousLinearMap.coe_mk', proj_xy_r90_mat, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.toLin'_apply, Matrix.mulVec_eq_sum, op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue,
      ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, Pi.add_apply, Pi.smul_apply,
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
          simp only [proj_rot, AddChar.coe_mk, rot3y_mat, rot3z_mat, cos_neg, sin_neg, neg_neg,
            ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_mk', proj_xy_r90_mat,
            LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Matrix.toLin'_apply,
            Matrix.mulVec_eq_sum, PiLp.toLp_apply, op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue,
            Matrix.cons_val_zero, neg_smul, Matrix.cons_val_one, Matrix.cons_val, zero_smul,
            add_zero, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Matrix.transpose_apply,
            Matrix.of_apply, smul_eq_mul, MulOpposite.op_add, MulOpposite.op_neg,
            MulOpposite.op_mul, neg_mul, MulOpposite.op_zero, zero_mul, neg_zero,
            MulOpposite.smul_eq_mul_unop, MulOpposite.unop_add, MulOpposite.unop_neg,
            MulOpposite.unop_mul, MulOpposite.unop_op, mul_zero, MulOpposite.op_one, mul_one,
            zero_add, ENNReal.toReal_ofNat, Nat.ofNat_pos, PiLp.norm_eq_sum, norm_eq_abs,
            rpow_ofNat, sq_abs, Fin.sum_univ_two, one_mul, even_two, Even.neg_pow, one_div]
          ring_nf
        _ ≤ N * ‖!₂[-sin θ, cos θ, 0]‖ := by assumption
        _ = N := by simp [Fin.sum_univ_three, PiLp.norm_eq_sum]

theorem dist_rot2_apply :
  ‖(rot2 α - rot2 α') v‖ = 2 * |sin ((α - α') / 2)| * ‖v‖ := by
    simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two, PiLp.norm_eq_sum]
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

theorem dist_rot3x_apply :
  ‖(rot3x α - rot3x α') v‖ = 2 * |sin ((α - α') / 2)| * ‖!₂[v 1, v 2]‖ := by
    simp only [AddChar.coe_mk, rot3x_mat, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Matrix.toLin'_apply, Matrix.mulVec_eq_sum,
      op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue, ENNReal.toReal_ofNat, Nat.ofNat_pos,
      PiLp.norm_eq_sum, Pi.add_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_one, mul_zero, add_zero, sub_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_neg, one_div, PiLp.toLp_apply,
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
    simp only [AddChar.coe_mk, rot3y_mat, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Matrix.toLin'_apply, Matrix.mulVec_eq_sum,
      op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue, ENNReal.toReal_ofNat, Nat.ofNat_pos,
      PiLp.norm_eq_sum, Pi.add_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_zero, add_zero, mul_neg, mul_one, zero_add,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_div, PiLp.toLp_apply,
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
    simp only [AddChar.coe_mk, rot3z_mat, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Matrix.toLin'_apply, Matrix.mulVec_eq_sum,
      op_smul_eq_smul, Fin.sum_univ_three, Fin.isValue, ENNReal.toReal_ofNat, Nat.ofNat_pos,
      PiLp.norm_eq_sum, Pi.add_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      smul_eq_mul, norm_eq_abs, rpow_ofNat, sq_abs, mul_neg, mul_zero, add_zero, mul_one, zero_add,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_div, PiLp.toLp_apply,
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
