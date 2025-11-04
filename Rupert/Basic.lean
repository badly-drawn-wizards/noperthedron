import Init.Data.Int.DivMod.Basic
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Init.Data.Int.DivMod.Basic

noncomputable section
open Real

notation "ℝ²" => Fin 2 → ℝ
notation "ℝ³" => Fin 3 → ℝ

namespace PreferComp
  variable {R A B : Type*}
  variable [Semiring R]
  variable [AddCommMonoid A] [Module R A] [TopologicalSpace A]
  @[scoped simp] def mul_eq_comp {f g : A →L[R] A} : g * f = g ∘L f := by rfl
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
#check fun α => rot3x α * rot3x α
#check fun α => rot2 α * rot2 α

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

def zhat : Fin 3 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1

@[simp]
def unit3 (θ φ : ℝ) : Fin 3 → ℝ :=
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
    | 1, 0 => -1
    | 1, 1 => 0

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
  grind only [cases Or]

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
    _ = (proj_xy_r90 ∘L rot3y φ ∘L rot3z a ∘L (s • rot3z b)) p := by simp
    _ = s • (proj_xy_r90 ∘L rot3y φ ∘L rot3z a ∘L rot3z b) p := by simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
    _ = s • (proj_xy_r90 ∘L rot3y φ ∘L (rot3z a ∘L rot3z b)) p := by simp
    _ = s • (proj_xy_r90 ∘L rot3y φ ∘L rot3z (a + b)) p := by simp [AddChar.map_add_eq_mul]
    _ = (proj_xy_r90 ∘L rot3y φ ∘L (s • rot3z (a + b))) p := by simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_apply]
  constructor <;> rintro (h|h|h) <;> rcases h with ⟨s, k, ⟨s_in, rfl⟩⟩
  · left
    use s, k-1
    grind
  · right; left
    use s, k-1
    grind
  · right; right
    use s, k-1
    grind
  · left
    use s, k+1
    grind
  · right; left
    use s, k+1
    grind
  · right; right
    use s, k+1
    grind

theorem lemma7_2 :
  (rot2 (α + π) ∘L proj_rot θ φ) '' noperthedron = (rot2 α ∘L proj_rot θ φ) '' noperthedron := by
    ext p
    constructor <;> rintro ⟨q, q_in, rfl⟩ <;> use -q <;> {
      constructor
      apply (noperthedron_point_symmetric q_in)
      simp [AddChar.map_add_eq_mul, map_neg]
    }

theorem lemma7_3 :
  (flip_y ∘L proj_rot θ φ) '' noperthedron = proj_rot (θ + π * 15⁻¹) (π - φ) '' noperthedron := by
    ext p
    simp only [Set.mem_image, SetLike.mem_coe, mem_noperthedron, proj_rot]
    constructor <;> rintro ⟨q, ⟨s,k,r,s_in,r_in,rfl⟩, rfl⟩ <;> simp only [↓existsAndEq, and_true]
    · sorry
    · sorry
