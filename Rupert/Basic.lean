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

@[reducible]
def rot2 : AddChar ℝ (Matrix (Fin 2) (Fin 2) ℝ) where
  toFun α := Matrix.of fun
    | 0, 0 => Real.cos α
    | 0, 1 => -Real.sin α
    | 1, 0 => Real.sin α
    | 1, 1 => Real.cos α
  map_zero_eq_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add_eq_mul' := by
    intro α β
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two,
      neg_mul, mul_neg, neg_add_rev, Real.sin_add, Real.cos_add
    ] <;> ring

@[simp]
theorem rot2_360 : rot2 (2 * Real.pi) = rot2 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot2_180 : rot2 Real.pi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot2_neg180 : rot2 Real.pi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot2_neg360 : rot2 (-(2 * Real.pi)) = rot2 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot2_k360 {k : ℤ} : rot2 (k * (2 * Real.pi)) = rot2 0 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_zero_eq_one, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul, AddChar.map_zero_eq_one]

@[reducible]
def rot3x : AddChar ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  toFun α := Matrix.of fun
    | 0, 0 => 1
    | 0, 1 => 0
    | 0, 2 => 0
    | 1, 0 => 0
    | 1, 1 => Real.cos α
    | 1, 2 => -Real.sin α
    | 2, 0 => 0
    | 2, 1 => Real.sin α
    | 2, 2 => Real.cos α
  map_zero_eq_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add_eq_mul' α β := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three,
      neg_mul, mul_neg, neg_add_rev, Real.sin_add, Real.cos_add
    ] <;> ring

@[simp]
theorem rot3x_360 : rot3x (2 * Real.pi) = rot3x 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot3x_neg360 : rot3x (-(2 * Real.pi)) = rot3x 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot3x_k360 {k : ℤ} : rot3x (k * (2 * Real.pi)) = rot3x 0 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_zero_eq_one, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul, AddChar.map_zero_eq_one]

@[reducible]
def rot3y : AddChar ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  toFun α := Matrix.of fun
    | 0, 0 => Real.cos α
    | 0, 1 => 0
    | 0, 2 => -Real.sin α
    | 1, 0 => 0
    | 1, 1 => 1
    | 1, 2 => 0
    | 2, 0 => Real.sin α
    | 2, 1 => 0
    | 2, 2 => Real.cos α
  map_zero_eq_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add_eq_mul' α β := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three,
      neg_mul, mul_neg, neg_add_rev, Real.sin_add, Real.cos_add
    ] <;> ring

@[simp]
theorem rot3y_360 : rot3y (2 * Real.pi) = rot3y 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot3y_neg360 : rot3y (-(2 * Real.pi)) = rot3y 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot3y_k360 {k : ℤ} : rot3y (k * (2 * Real.pi)) = rot3y 0 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_zero_eq_one, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul, AddChar.map_zero_eq_one]

@[reducible]
def rot3z : AddChar ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  toFun α := Matrix.of fun
    | 0, 0 => Real.cos α
    | 0, 1 => -Real.sin α
    | 0, 2 => 0
    | 1, 0 => Real.sin α
    | 1, 1 => Real.cos α
    | 1, 2 => 0
    | 2, 0 => 0
    | 2, 1 => 0
    | 2, 2 => 1
  map_zero_eq_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add_eq_mul' α β := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three,
      neg_mul, mul_neg, neg_add_rev, Real.sin_add, Real.cos_add
    ] <;> ring

@[simp]
theorem rot3z_360 : rot3z (2 * Real.pi) = rot3z 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot3z_neg360 : rot3z (-(2 * Real.pi)) = rot3z 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem rot3z_k360 {k : ℤ} : rot3z (k * (2 * Real.pi)) = rot3z 0 := by
  induction k with
  | zero => simp
  | succ n h => rw [←h]; simp [right_distrib, AddChar.map_zero_eq_one, AddChar.map_add_eq_mul]
  | pred n h =>
      rw [←h]
      simp [sub_eq_add_neg, right_distrib, AddChar.map_add_eq_mul, AddChar.map_zero_eq_one]

def zhat : Matrix (Fin 3) (Fin 1) ℝ :=
  Matrix.of fun
    | 0, 0 => 0
    | 1, 0 => 0
    | 2, 0 => 1

def unit3 (θ φ : ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  (zhat.transpose * rot3y φ * rot3z (-θ)).transpose

def proj_xy_r90 : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun
    | 0, 0 => 0
    | 0, 1 => 1
    | 0, 2 => 0
    | 1, 0 => -1
    | 1, 1 => 0
    | 1, 2 => 0

@[reducible]
def flip_y : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => 1
    | 0, 1 => 0
    | 1, 0 => -1
    | 1, 1 => 0

@[reducible]
def proj_rot (θ φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  proj_xy_r90 * rot3y φ * rot3z (-θ)

theorem rot_proj_rot : rot2 α * proj_rot θ φ = proj_xy_r90 * rot3z α * rot3y φ * rot3z (-θ) := by
  ext i j
  unfold proj_rot
  unfold proj_xy_r90
  fin_cases i <;> fin_cases j <;> simp only [
    AddChar.coe_mk, neg_neg, Fin.zero_eta, Fin.isValue,
    Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Fin.sum_univ_three,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, mul_neg, neg_mul
  ] <;> ring

def convex_position (𝕜 V : Type) [PartialOrder 𝕜] [AddCommMonoid 𝕜] [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] (P : Set V) : Prop :=
  ∀ p ∈ P,
    p ∉ convexHull 𝕜 (P \ (Set.singleton p))

class PointSymmetric (V : Type) [Neg V] (P : Set V) where
  point_symmetric : p ∈ P → -p ∈ P

@[simp]
theorem mem_point_symmetric [InvolutiveNeg V] [PointSymmetric V P] : p ∈ P ↔ -p ∈ P := by
  constructor <;> intro h
  · exact PointSymmetric.point_symmetric h
  · rw [←(neg_neg p)]; exact PointSymmetric.point_symmetric h


notation "ℝ³" => Matrix (Fin 3) (Fin 1) ℝ
infixl:80 " *'' " => fun m s => (m * ·) '' s

def rupert' (P : Set ℝ³) :=
    ∃ (α θ₁ φ₁ θ₂ φ₂ : ℝ), ∀ p ∈ P,
    rot2 α * proj_rot θ₁ φ₁ * p ∈ (interior $ convexHull ℝ $ proj_rot θ₂ φ₂ *'' P)

def C₁ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun
  | 0, 0 => 152024884 / 259375205
  | 1, 0 => 0
  | 2, 0 => 210152163 / 259375205

def C₂ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun
  | 0, 0 => 6632738028e-10
  | 1, 0 => 6106948881e-10
  | 2, 0 => 3980949609e-10

def C₃ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun
  | 0, 0 => 8193990033e-10
  | 1, 0 => 5298215096e-10
  | 2, 0 => 1230614493e-10

def noperthedron_seed : Finset ℝ³ := {C₁, C₂, C₃}

@[simp]
def mem_noperthedron_seed (p : ℝ³) :
    p ∈ noperthedron_seed ↔ p = C₁ ∨ p = C₂ ∨ p = C₃ := by
    unfold noperthedron_seed
    grind only [= Finset.mem_insert, = Set.mem_singleton_iff, = Finset.insert_eq_of_mem,
      = Finset.mem_singleton, cases Or]

def noperthedron : Finset ℝ³ :=
    ({1,-1} : Finset ℤ) ×ˢ (Finset.range 15) ×ˢ noperthedron_seed
      |>.image fun (s, (k, p)) => s • rot3z (k * (1/15) * (2 * Real.pi)) * p

def mem_noperthedron' (p : ℝ³) :
    p ∈ noperthedron ↔
    ∃ (s : ℤ) (k : ℕ) (q : ℝ³),
      s ∈ ({1,-1} : Finset ℤ) ∧
      k < 15 ∧
      q ∈ noperthedron_seed ∧
      p = s • rot3z (k * (1/15) * (2 * Real.pi)) * q := by
  unfold noperthedron
  simp only [zsmul_eq_mul, Int.reduceNeg, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_range, Prod.exists]
  grind only [cases Or]

@[simp]
def mem_noperthedron (p : ℝ³) :
    p ∈ noperthedron ↔
    ∃ (s : ℤ) (k : ℤ) (q : ℝ³),
      s ∈ ({1,-1} : Finset ℤ) ∧
      q ∈ noperthedron_seed ∧
      p = s • rot3z (k * (1/15) * (2 * Real.pi)) * q := by
  rw [mem_noperthedron']
  constructor
  · rintro ⟨s, k, q, ⟨s_in, k_in, q_in, rfl⟩⟩; exists s, k, q
  · rintro ⟨s, k, q, ⟨s_in, q_in, rfl⟩⟩
    let d := k / 15
    let k' := (k % 15).natAbs
    exists s, k', q
    suffices rot3z (k * (1/15) * (2 * Real.pi)) = rot3z (k' * (1/15) * (2 * Real.pi)) by grind only
    calc
      rot3z (k * (1/15) * (2 * Real.pi)) = rot3z ((d * 15 + k % 15 : ℤ) * (1/15) * (2 * Real.pi)) := by rw [Int.ediv_mul_add_emod]
      _ = rot3z (((d * 15 : ℤ) + (k % 15 : ℤ)) * (1/15) * (2 * Real.pi)) := by simp
      _ = rot3z (d * (2 * Real.pi) + (k % 15 : ℤ) * (1/15) * (2 * Real.pi)) := by simp [right_distrib]
      _ = rot3z ((k % 15 : ℤ) * (1/15) * (2 * Real.pi)) := by simp [AddChar.map_add_eq_mul]
      _ = rot3z (k' * (1/15) * (2 * Real.pi)) := by rw [( calc (k % 15 : ℤ) = k' := by grind)]; norm_cast


instance point_symmetric_noperthedron : PointSymmetric ℝ³ (SetLike.coe noperthedron) where
  point_symmetric p_in := by
    simp only [SetLike.mem_coe, mem_noperthedron] at *
    rcases p_in with ⟨s, k, q, ⟨s_in, q_in, rfl⟩⟩
    exists -s, k, q
    simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton] at s_in
    rcases s_in with rfl|rfl <;> simp only [neg_smul, one_smul, Matrix.neg_mul] <;> grind

theorem lemma7_1 :
  proj_rot (θ + 2/15*Real.pi) φ *'' SetLike.coe noperthedron = proj_rot θ φ *'' SetLike.coe noperthedron := by
  ext p
  simp only [Set.mem_image, SetLike.mem_coe, mem_noperthedron, mem_noperthedron_seed,
    ↓existsAndEq, and_true, and_or_left, or_and_right, exists_or, proj_rot, Matrix.mul_smul, Matrix.smul_mul]

  have h (p : ℝ³) (s : ℤ) a b := calc
    s • (proj_xy_r90 * rot3y φ * rot3z a * (rot3z b * p)) = _ := by rfl
    _ = s • (proj_xy_r90 * rot3y φ * (rot3z a * rot3z b * p)) := by simp [Matrix.mul_assoc]
    _ = s • (proj_xy_r90 * rot3y φ * (rot3z (a + b) * p)) := by simp [AddChar.map_add_eq_mul]
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
  (rot2 (α + Real.pi) * proj_rot θ φ) *'' SetLike.coe noperthedron = (rot2 α * proj_rot θ φ)  *'' SetLike.coe noperthedron
    := by
    ext p
    simp only [AddChar.map_add_eq_mul, rot2_180, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, Set.mem_image]
    constructor <;> rintro ⟨q, q_in, rfl⟩ <;> use -q
    · constructor
      apply (PointSymmetric.point_symmetric q_in)
      simp
    · constructor
      apply (PointSymmetric.point_symmetric q_in)
      simp

-- theorem lemma7_3 :
--   flip_y * proj_rot θ φ *'' SetLike.coe noperthedron = proj_rot
