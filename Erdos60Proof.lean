import Mathlib

/-!
# A formal refutation of Erdős problem 60

The proof uses the ordinary four-cycle count and the actual extremal number.
A finite-field splitting construction and extremal exchange estimates reduce
the asserted square-root lower bound to a regular binary completion matrix.
The residual graph is a union of cycles. Cyclic transition counts and a
rational trace argument bound the extremal excess by three, contradicting
the quantitative lower bound on the selected square-dyadic sequence.

The original-problem statement and public proof interface are in
`OriginalStatement.lean` and `JSP79.lean`.
-/

namespace Bounty
open scoped Classical




/-
The following polarity foundations adapt public work by Robert Huynh,
https://github.com/roberthuynh/erdos/tree/main/problems/60,
from Polarity.lean, PolarityDegree.lean, PolarityAbsoluteBound.lean,
and FiniteFieldPolarity.lean. That source is licensed under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0.
The original downloaded source snapshots are retained in the private audit.
-/

namespace Erdos60.Geometry

variable {P L : Type*} [Membership P L]

/-- A point-to-line equivalence with symmetric incidence is precisely the
point-to-line part of a polarity. Its inverse specifies the line-to-point part. -/
structure Polarity where
  line : P ≃ L
  reciprocal : ∀ x y : P, x ∈ line y ↔ y ∈ line x

def Polarity.graph (π : Polarity (P := P) (L := L)) : SimpleGraph P where
  Adj x y := x ≠ y ∧ x ∈ π.line y
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, (π.reciprocal x y).mp h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem Polarity.adj_iff (π : Polarity (P := P) (L := L)) (x y : P) :
    π.graph.Adj x y ↔ x ≠ y ∧ x ∈ π.line y := Iff.rfl

/-- The incidence uniqueness axiom proves the actual graph has at most one
common neighbor for distinct vertices. No completion theorem is assumed. -/
theorem Polarity.common_neighbor_unique [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {x y u v : P} (hxy : x ≠ y)
    (hxu : π.graph.Adj x u) (hyu : π.graph.Adj y u)
    (hxv : π.graph.Adj x v) (hyv : π.graph.Adj y v) : u = v := by
  have hu := (π.reciprocal x u).mp hxu.2
  have hu' := (π.reciprocal y u).mp hyu.2
  have hv := (π.reciprocal x v).mp hxv.2
  have hv' := (π.reciprocal y v).mp hyv.2
  rcases Configuration.Nondegenerate.eq_or_eq hu hv hu' hv' with h | h
  · exact h
  · exact False.elim (hxy (π.line.injective h))

/-- No ordinary four-cycle, expressed directly with its four edges. This
form avoids any induced-cycle convention or labelled-copy normalization. -/
theorem Polarity.no_four_cycle [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {a b c d : P}
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : π.graph.Adj a b) (hbc : π.graph.Adj b c)
    (hcd : π.graph.Adj c d) (hda : π.graph.Adj d a) : False := by
  exact hbd (π.common_neighbor_unique hac hab hbc.symm hda.symm hcd)

theorem Polarity.card_vertices [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (_π : Polarity (P := P) (L := L)) :
    Fintype.card P = Configuration.ProjectivePlane.order P L ^ 2 +
      Configuration.ProjectivePlane.order P L + 1 :=
  Configuration.ProjectivePlane.card_points P L


end Erdos60.Geometry

namespace Erdos60.Geometry
variable {P L : Type*} [Membership P L]

def Polarity.Absolute (π : Polarity (P := P) (L := L)) (x : P) : Prop := x ∈ π.line x

theorem Polarity.degree_add_diagonal [Fintype P]
    (π : Polarity (P := P) (L := L)) (x : P) :
    letI : Decidable (π.Absolute x) := Classical.propDecidable _
    letI := Classical.decRel π.graph.Adj
    π.graph.degree x + (if π.Absolute x then 1 else 0) =
      Configuration.pointCount P (π.line x) := by
  classical
  let s : Finset P := Finset.univ.filter (fun y => y ∈ π.line x)
  have hn : π.graph.neighborFinset x = s.erase x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Polarity.adj_iff,
      Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, s]
    constructor
    · rintro ⟨hne, hi⟩
      exact ⟨hne.symm, (π.reciprocal x y).mp hi⟩
    · rintro ⟨hne, hi⟩
      exact ⟨hne.symm, (π.reciprocal y x).mp hi⟩
  have hs : s.card = Configuration.pointCount P (π.line x) := by
    simp [s, Configuration.pointCount, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn, ← hs]
  by_cases hx : π.Absolute x
  · have hx' : x ∈ s := by simpa [s, Polarity.Absolute] using hx
    simp only [ite_eq_left hx]
    exact Finset.card_erase_add_one hx'
  · have hx' : x ∉ s := by simpa [s, Polarity.Absolute] using hx
    simp [hx, Finset.erase_eq_of_notMem hx']


end Erdos60.Geometry

namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L]

/-- Exact degree sum with the removed absolute diagonals retained. -/
theorem Polarity.twice_edges_add_absolute [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L)) :
    2 * π.graph.edgeFinset.card + Nat.card {a : P // π.Absolute a} =
      (Configuration.ProjectivePlane.order P L + 1) *
      (Configuration.ProjectivePlane.order P L ^ 2 +
        Configuration.ProjectivePlane.order P L + 1) := by
  classical
  have hsum : ∑ x : P, (π.graph.degree x + if π.Absolute x then 1 else 0) =
      ∑ _x : P, (Configuration.ProjectivePlane.order P L + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    exact (π.degree_add_diagonal x).trans
      (Configuration.ProjectivePlane.pointCount_eq (P := P) (π.line x))
  have hdiag : (∑ x : P, if π.Absolute x then 1 else 0) =
      Nat.card {a : P // π.Absolute a} := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_add_distrib, π.graph.sum_degrees_eq_twice_card_edges, hdiag] at hsum
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Configuration.ProjectivePlane.card_points P L, Nat.mul_comm] using hsum

end Erdos60.Geometry

namespace Erdos60.Construction
open scoped LinearAlgebra.Projectivization
open Projectivization Matrix
variable (K : Type*) [Field K]
abbrev Point := ℙ K (Fin 3 → K)

def dotPolarity : Erdos60.Geometry.Polarity (P := Point K) (L := Point K) where
  line := Equiv.refl _
  reciprocal := fun _x _y => Projectivization.orthogonal_comm

noncomputable def absoluteLine : Point K := mk K ![1,1,1] (by simp)

theorem absolute_iff_on_line [CharP K 2] (p : Point K) :
    p ∈ (dotPolarity K).line p ↔ p ∈ absoluteLine K := by
  induction p using Projectivization.ind with | h v hv =>
  change orthogonal (mk K v hv) (mk K v hv) ↔ orthogonal (mk K v hv) (absoluteLine K)
  rw [orthogonal_mk, absoluteLine, orthogonal_mk]
  simp only [dotProduct, Fin.sum_univ_succ, 
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.sum_univ_zero, add_zero, mul_one]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro h
    have hs : (v 0 + v 1 + v 2)^2 = 0 := by
      calc
        _ = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 +
          2 * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) := by ring
        _ = 0 := by rw [htwo, zero_mul, add_zero]; simpa [add_assoc] using h
    have hz : v 0 + v 1 + v 2 = 0 := (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp hs
    simpa [add_assoc] using hz
  · intro h
    have heq : (v 0 + v 1 + v 2)^2 = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
      calc
        _ = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + 2 * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) := by ring
        _ = _ := by rw [htwo, zero_mul, add_zero]
    rw [add_assoc, h, zero_pow (by decide : (2:ℕ) ≠ 0)] at heq
    simpa [add_assoc] using heq.symm

theorem plane_order [Finite K] [DecidableEq K] :
    Configuration.ProjectivePlane.order (Point K) (Point K) = Nat.card K := by
  classical
  let : Fintype (Point K) := Fintype.ofFinite _
  have hp := Configuration.ProjectivePlane.card_points (Point K) (Point K)
  have hc := Projectivization.card_of_finrank K (Fin 3 → K)
    (by simp : Module.finrank K (Fin 3 → K) = 3)
  have hc' : Nat.card (Point K) = Nat.card K ^ 2 + Nat.card K + 1 := by
    simpa [Finset.sum_range_succ, pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using hc
  rw [Nat.card_eq_fintype_card] at hc'
  nlinarith

theorem absolute_count [Finite K] [DecidableEq K] [CharP K 2] :
    Nat.card {p : Point K // p ∈ (dotPolarity K).line p} = Nat.card K + 1 := by
  have he : {p : Point K // p ∈ (dotPolarity K).line p} ≃
      {p : Point K // p ∈ absoluteLine K} :=
    Equiv.subtypeEquivRight (absolute_iff_on_line K)
  rw [Nat.card_congr he]
  change Configuration.pointCount (Point K) (absoluteLine K) = _
  rw [Configuration.ProjectivePlane.pointCount_eq, plane_order]



/-- Actual finite-field polarity at every nontrivial power of two, with
its order and number of absolute points. -/
theorem power_two_construction (k : ℕ) (hk : k ≠ 0) :
    ∃ π : Erdos60.Geometry.Polarity
        (P := Point (GaloisField 2 k)) (L := Point (GaloisField 2 k)),
      Configuration.ProjectivePlane.order
        (Point (GaloisField 2 k)) (Point (GaloisField 2 k)) = 2^k ∧
      Nat.card {p : Point (GaloisField 2 k) // p ∈ π.line p} = 2^k + 1 ∧
      ∃ l : Point (GaloisField 2 k), ∀ p, p ∈ π.line p ↔ p ∈ l := by
  classical
  refine ⟨dotPolarity _, ?_, ?_, absoluteLine _, absolute_iff_on_line _⟩
  · rw [plane_order, GaloisField.card 2 k hk]
  · rw [absolute_count, GaloisField.card 2 k hk]

end Erdos60.Construction

namespace Erdos60Private

open Filter SimpleGraph Matrix
open scoped BigOperators Classical

noncomputable section

theorem edgeSet_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.edgeSet.ncard = G.edgeFinset.card := by
  classical
  rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_edgeSet]

/-- The cycle count in the pinned Conjectures.io statement. -/
def fourCycleCopies {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  {H : G.Subgraph | Nonempty (H.coe ≃g cycleGraph 4)}.ncard

/-- Mathlib's copy count agrees with the orientation of isomorphisms in the target. -/
theorem fourCycleCopies_eq_copyCount {n : ℕ} (G : SimpleGraph (Fin n)) :
    fourCycleCopies G = G.copyCount (cycleGraph 4) := by
  classical
  unfold fourCycleCopies SimpleGraph.copyCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext H
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq]
  exact ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩

theorem fourCycleCopies_eq_zero_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    fourCycleCopies G = 0 ↔ (cycleGraph 4).Free G := by
  rw [fourCycleCopies_eq_copyCount, SimpleGraph.copyCount_eq_zero]

/-- An ambient graph isomorphism induces an equivalence of its subgraphs. -/
def subgraphMapEquiv {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.Subgraph ≃ H.Subgraph where
  toFun K := K.map e.toHom
  invFun K := K.map e.symm.toHom
  left_inv K := by
    change (K.map e.toHom).map e.symm.toHom = K
    rw [← SimpleGraph.Subgraph.map_comp, e.symm_toHom_comp_toHom,
      SimpleGraph.Subgraph.map_id]
  right_inv K := by
    change (K.map e.symm.toHom).map e.toHom = K
    rw [← SimpleGraph.Subgraph.map_comp, e.toHom_comp_symm_toHom,
      SimpleGraph.Subgraph.map_id]

/-- Counting cycle subgraphs is invariant under relabelling the ambient vertices. -/
theorem copyCount_iso {V W U : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (F : SimpleGraph U) :
    G.copyCount F = H.copyCount F := by
  classical
  have hCount (K : SimpleGraph V) : K.copyCount F =
      {L : K.Subgraph | Nonempty (F ≃g L.coe)}.ncard := by
    unfold SimpleGraph.copyCount
    rw [← Set.ncard_coe_finset]
    congr 1
    ext L
    simp
  have hCountH : H.copyCount F =
      {L : H.Subgraph | Nonempty (F ≃g L.coe)}.ncard := by
    unfold SimpleGraph.copyCount
    rw [← Set.ncard_coe_finset]
    congr 1
    ext L
    simp
  rw [hCount, hCountH]
  apply Set.ncard_congr'
  refine {
    toFun := fun K => ⟨K.val.map e.toHom, ?_⟩
    invFun := fun K => ⟨K.val.map e.symm.toHom, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · obtain ⟨f⟩ := K.property
    exact ⟨(e.toCopy.isoSubgraphMap K.val).comp f⟩
  · obtain ⟨f⟩ := K.property
    exact ⟨(e.symm.toCopy.isoSubgraphMap K.val).comp f⟩
  · intro K
    apply Subtype.ext
    exact (subgraphMapEquiv e).left_inv K.val
  · intro K
    apply Subtype.ext
    exact (subgraphMapEquiv e).right_inv K.val

/-- The mathematical proposition in the pinned statement. -/
def ClaimedBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
          c * Real.sqrt (n : ℝ) ≤ (fourCycleCopies G : ℝ)

/-- The edge count of the binary polarity graph at the plane order. -/
def planeEdgeCount (q : ℕ) : ℕ := q * (q + 1) ^ 2 / 2

/-- Excess over the polarity construction at the above-plane vertex count. -/
def abovePlaneExcess (q : ℕ) : ℕ :=
  extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) - planeEdgeCount q

/-- The polarity edge expression is integral for every integer parameter. -/
theorem twice_planeEdgeCount (q : ℕ) : 2 * planeEdgeCount q = q * (q + 1) ^ 2 := by
  have hEven : Even (q * (q + 1) ^ 2) := by
    rw [pow_two, ← mul_assoc]
    exact (Nat.even_mul_succ_self q).mul_right (q + 1)
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp hEven)

/-- The tie-breaking objective used to select an edge extremizer in the manuscript. -/
def extremalObjective {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (∑ v, G.degree v ^ 2) + 2 * G.copyCount (⊤ : SimpleGraph (Fin 3))

/-- Signed deficiency retains the negative value at vertices above degree q+1. -/
def signedDeficiency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : ℤ := by
  classical
  exact (q : ℤ) + 1 - G.degree v

/-- The global signed-deficiency sum is an exact handshaking identity. -/
theorem sum_signedDeficiency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    (∑ v, signedDeficiency q G v) =
      ((q : ℤ) + 1) * n - 2 * G.edgeSet.ncard := by
  classical
  calc
    (∑ v, signedDeficiency q G v) =
        ((q : ℤ) + 1) * n - ((∑ v, G.degree v : ℕ) : ℤ) := by
      simp [signedDeficiency, Finset.sum_sub_distrib, mul_comm]
    _ = ((q : ℤ) + 1) * n - 2 * G.edgeSet.ncard := by
      rw [G.sum_degrees_eq_twice_card_edges]
      simp only [Nat.cast_mul, Nat.cast_ofNat, edgeSet_ncard]

/-- The signed diagonal correction gives constant row sums. -/
def weightedAdjacency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℤ :=
  G.adjMatrix ℤ + Matrix.diagonal (signedDeficiency q G)

/-- The all-ones matrix. -/
def allOnesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun _ _ => 1

/-- The residual matrix used in the extremal argument. -/
def weightedResidual {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal (fun _ : Fin n => (q : ℤ)) + allOnesMatrix n -
    weightedAdjacency q G * weightedAdjacency q G

theorem weightedAdjacency_symmetric {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    (weightedAdjacency q G).IsSymm :=
  G.isSymm_adjMatrix.add (Matrix.isSymm_diagonal _)

theorem weightedAdjacency_trace {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    Matrix.trace (weightedAdjacency q G) = ∑ v, signedDeficiency q G v := by
  rw [weightedAdjacency, Matrix.trace_add, G.trace_adjMatrix ℤ, zero_add,
    Matrix.trace_diagonal]

theorem weightedAdjacency_row_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    weightedAdjacency q G *ᵥ (1 : Fin n → ℤ) = fun _ => (q : ℤ) + 1 := by
  ext v
  simp [weightedAdjacency, Matrix.add_mulVec, Matrix.mulVec_diagonal,
    signedDeficiency]

theorem weightedAdjacency_square_row_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    (weightedAdjacency q G * weightedAdjacency q G) *ᵥ (1 : Fin n → ℤ) =
      fun _ => ((q : ℤ) + 1) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, weightedAdjacency_row_sum]
  have hConstant : (fun _ : Fin n => (q : ℤ) + 1) =
      ((q : ℤ) + 1) • (1 : Fin n → ℤ) := by ext; simp
  rw [hConstant, Matrix.mulVec_smul, weightedAdjacency_row_sum]
  ext v
  simp [pow_two]

theorem weightedResidual_row_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    weightedResidual q G *ᵥ (1 : Fin n → ℤ) =
      fun _ => (q : ℤ) + n - ((q : ℤ) + 1) ^ 2 := by
  rw [weightedResidual, Matrix.sub_mulVec, Matrix.add_mulVec,
    weightedAdjacency_square_row_sum]
  ext v
  simp [Matrix.mulVec, dotProduct, allOnesMatrix]

theorem above_plane_residual_row_sum (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) :
    weightedResidual q G *ᵥ (1 : Fin (q ^ 2 + q + 2) → ℤ) = 1 := by
  rw [weightedResidual_row_sum]
  ext v
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Pi.one_apply]
  ring

theorem weightedAdjacency_commutes_ones {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    weightedAdjacency q G * allOnesMatrix n =
      allOnesMatrix n * weightedAdjacency q G := by
  have hRow (v : Fin n) : (∑ w, weightedAdjacency q G v w) = (q : ℤ) + 1 := by
    have h := congrFun (weightedAdjacency_row_sum q G) v
    simpa [Matrix.mulVec, dotProduct] using h
  have hColumn (v : Fin n) : (∑ w, weightedAdjacency q G w v) = (q : ℤ) + 1 := by
    calc
      _ = ∑ w, weightedAdjacency q G v w := by
        apply Finset.sum_congr rfl
        intro w _
        exact (weightedAdjacency_symmetric q G).apply v w
      _ = _ := hRow v
  ext i j
  simp only [Matrix.mul_apply, allOnesMatrix, mul_one, one_mul]
  exact (hRow i).trans (hColumn j).symm

/-- Constant row sums and symmetry imply the commutator identity used locally. -/
theorem weightedAdjacency_commutes_residual {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) :
    weightedAdjacency q G * weightedResidual q G =
      weightedResidual q G * weightedAdjacency q G := by
  have hDiagonal : weightedAdjacency q G * Matrix.diagonal (fun _ => (q : ℤ)) =
      Matrix.diagonal (fun _ => (q : ℤ)) * weightedAdjacency q G := by
    ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  unfold weightedResidual
  rw [mul_sub, mul_add, sub_mul, add_mul, hDiagonal,
    weightedAdjacency_commutes_ones, mul_assoc]

theorem weightedResidual_diagonal {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) :
    weightedResidual q G v v = signedDeficiency q G v - signedDeficiency q G v ^ 2 := by
  have hSquare : (weightedAdjacency q G * weightedAdjacency q G) v v =
      (G.degree v : ℤ) + signedDeficiency q G v ^ 2 := by
    rw [weightedAdjacency, add_mul, mul_add, mul_add]
    simp [-SimpleGraph.adjMatrix_mul_apply, -SimpleGraph.mul_adjMatrix_apply,
      Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      G.adjMatrix_mul_self_apply_self, pow_two]
  simp only [weightedResidual, Matrix.sub_apply, Matrix.add_apply,
    Matrix.diagonal_apply_eq, allOnesMatrix, hSquare]
  simp only [signedDeficiency]
  ring

/-- The four-cycle has an edge, so the extremal existence theorem applies. -/
theorem cycleGraph_four_ne_bot : cycleGraph 4 ≠ ⊥ := by
  intro h
  have hEdge : (cycleGraph 4).Adj 0 1 := by decide
  rw [h] at hEdge
  exact hEdge

/-- The secondary objective can be minimized over genuine edge extremizers. -/
theorem exists_minimizing_extremizer (n : ℕ)
    (score : SimpleGraph (Fin n) → ℕ) :
    ∃ G : SimpleGraph (Fin n),
      (cycleGraph 4).Free G ∧
      G.edgeSet.ncard = extremalNumber n (cycleGraph 4) ∧
      ∀ H : SimpleGraph (Fin n),
        (cycleGraph 4).Free H →
        H.edgeSet.ncard = extremalNumber n (cycleGraph 4) →
        score G ≤ score H := by
  classical
  have hExists : ∃ k : ℕ, ∃ G : SimpleGraph (Fin n),
      (cycleGraph 4).Free G ∧
      G.edgeSet.ncard = extremalNumber n (cycleGraph 4) ∧ score G = k := by
    obtain ⟨G, _, hG⟩ :=
      SimpleGraph.exists_isExtremal_free (V := Fin n) cycleGraph_four_ne_bot
    refine ⟨score G, G, hG.prop, ?_, rfl⟩
    have hEdges := SimpleGraph.card_edgeFinset_of_isExtremal_free hG
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at hEdges
    simpa only [Fintype.card_fin] using hEdges
  obtain ⟨G, hFree, hEdges, hScore⟩ := Nat.find_spec hExists
  refine ⟨G, hFree, hEdges, ?_⟩
  intro H hHFree hHEdges
  rw [hScore]
  exact Nat.find_min' hExists ⟨H, hHFree, hHEdges, rfl⟩

/-- Four edges on four distinct vertices give an ordinary copy of the four-cycle. -/
theorem contains_four_cycle {V : Type*} (G : SimpleGraph V)
    (a b c d : V) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) :
    cycleGraph 4 ⊑ G := by
  classical
  have hab' := G.ne_of_adj hab
  have hbc' := G.ne_of_adj hbc
  have hcd' := G.ne_of_adj hcd
  have hda' := G.ne_of_adj hda
  refine ⟨{
    toHom := {
      toFun := ![a, b, c, d]
      map_rel' := ?_ }
    injective' := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hab
      | exact hab.symm
      | exact hbc
      | exact hbc.symm
      | exact hcd
      | exact hcd.symm
      | exact hda
      | exact hda.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Every pair of distinct vertices in a four-cycle-free graph has at most one common neighbor. -/
theorem common_neighbor_unique {V : Type*} (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hux : G.Adj u x) (hvx : G.Adj v x)
    (huy : G.Adj u y) (hvy : G.Adj v y) : x = y := by
  by_contra hxy
  exact hFree (contains_four_cycle G u x v y huv hxy hux hvx.symm hvy huy.symm)

/-- The codegree formulation used throughout the proposed extremal argument. -/
theorem free_iff_common_neighbor_unique {V : Type*} (G : SimpleGraph V) :
    (cycleGraph 4).Free G ↔
      ∀ u v : V, u ≠ v → ∀ x y : V,
        G.Adj u x → G.Adj v x → G.Adj u y → G.Adj v y → x = y := by
  constructor
  · intro hFree u v huv x y hux hvx huy hvy
    exact common_neighbor_unique G hFree huv hux hvx huy hvy
  · intro hUnique hContains
    obtain ⟨f⟩ := hContains
    have h02 : f 0 ≠ f 2 := f.injective.ne (by decide)
    have h13 : f 1 ≠ f 3 := f.injective.ne (by decide)
    apply h13
    exact hUnique (f 0) (f 2) h02 (f 1) (f 3)
      (f.toHom.map_rel' (by decide))
      (f.toHom.map_rel' (by decide))
      (f.toHom.map_rel' (by decide))
      (f.toHom.map_rel' (by decide))

/-- Number of common neighbors, including the usual diagonal convention. -/
def codegree {n : ℕ} (G : SimpleGraph (Fin n)) (v w : Fin n) : ℕ :=
  (G.neighborFinset v ∩ G.neighborFinset w).card

theorem codegree_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v w : Fin n) (hvw : v ≠ w) :
    codegree G v w ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact common_neighbor_unique G hFree hvw
    ((G.mem_neighborFinset v a).mp (Finset.mem_inter.mp ha).1)
    ((G.mem_neighborFinset w a).mp (Finset.mem_inter.mp ha).2)
    ((G.mem_neighborFinset v b).mp (Finset.mem_inter.mp hb).1)
    ((G.mem_neighborFinset w b).mp (Finset.mem_inter.mp hb).2)

theorem adjMatrix_square_codegree {n : ℕ} (G : SimpleGraph (Fin n)) (v w : Fin n) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ) v w = (codegree G v w : ℤ) := by
  classical
  rw [G.adjMatrix_mul_apply]
  have hEntry (x : Fin n) : G.adjMatrix ℤ x w =
      if x ∈ G.neighborFinset w then (1 : ℤ) else 0 := by
    rw [G.adjMatrix_apply, G.adj_comm x w]
    simp only [G.mem_neighborFinset w x]
  simp_rw [hEntry]
  rw [← Finset.sum_filter]
  have hFilter : (G.neighborFinset v).filter (fun x => x ∈ G.neighborFinset w) =
      G.neighborFinset v ∩ G.neighborFinset w := by ext; simp
  rw [hFilter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, codegree]

/-- Graph of distinct pairs with no common neighbor. -/
def zeroCodegreeGraph {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ codegree G v w = 0
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, by simpa [codegree, Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The exact second-walk matrix identity used by the deficiency argument. -/
theorem adjMatrix_square_defect_identity {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G) :
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      Matrix.diagonal (fun _ : Fin n => (q : ℤ)) + allOnesMatrix n -
        ((zeroCodegreeGraph G).adjMatrix ℤ + Matrix.diagonal (signedDeficiency q G)) := by
  classical
  ext v w
  by_cases hvw : v = w
  · subst w
    rw [G.adjMatrix_mul_self_apply_self]
    simp [Matrix.sub_apply, Matrix.add_apply, allOnesMatrix, signedDeficiency]
  · rw [adjMatrix_square_codegree]
    have hZero : (zeroCodegreeGraph G).adjMatrix ℤ v w =
        if v ≠ w ∧ codegree G v w = 0 then 1 else 0 := by
      rw [(zeroCodegreeGraph G).adjMatrix_apply]
      by_cases h : v ≠ w ∧ codegree G v w = 0 <;> simp [zeroCodegreeGraph, h]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply,
      ite_eq_right hvw, allOnesMatrix, zero_add, add_zero]
    rw [hZero]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (codegree_le_one G hFree v w hvw) with hc | hc
    all_goals simp [hvw, hc]

/-- The off-diagonal residual entry retains both endpoint deficiencies. -/
theorem weightedResidual_off_diagonal {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w) :
    weightedResidual q G v w = 1 - (G.adjMatrix ℤ * G.adjMatrix ℤ) v w -
      G.adjMatrix ℤ v w * (signedDeficiency q G v + signedDeficiency q G w) := by
  simp [-SimpleGraph.adjMatrix_mul_apply, -SimpleGraph.mul_adjMatrix_apply,
    weightedResidual, weightedAdjacency, allOnesMatrix, add_mul, mul_add,
    Matrix.mul_diagonal, Matrix.diagonal_mul, hvw]
  ring

/-- The zero-codegree row count is the exact signed-deficiency identity of the manuscript. -/
theorem zeroCodegree_degree_identity (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) :
    ((zeroCodegreeGraph G).degree v : ℤ) = 1 + q * signedDeficiency q G v +
      ∑ w ∈ G.neighborFinset v, signedDeficiency q G w := by
  have hA2 : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ 1) v =
      ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ) := by
    rw [← Matrix.mulVec_mulVec, G.adjMatrix_mulVec_apply]
    simp
  have hJ : (allOnesMatrix (q ^ 2 + q + 2) *ᵥ 1) v =
      (q ^ 2 + q + 2 : ℕ) := by
    simp [allOnesMatrix, Matrix.mulVec, dotProduct]
  have hEq := congrArg (fun M : Matrix (Fin (q ^ 2 + q + 2))
      (Fin (q ^ 2 + q + 2)) ℤ => (M *ᵥ 1) v)
    (adjMatrix_square_defect_identity q G hFree)
  rw [hA2, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec] at hEq
  have hZeroRow : ((zeroCodegreeGraph G).adjMatrix ℤ *ᵥ (1 : Fin (q ^ 2 + q + 2) → ℤ)) v =
      ((zeroCodegreeGraph G).degree v : ℤ) := by
    rw [(zeroCodegreeGraph G).adjMatrix_mulVec_apply]
    simp
  simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_diagonal,
    Pi.one_apply, hZeroRow, mul_one, hJ] at hEq
  have hSum : (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) =
      ((q : ℤ) + 1) * G.degree v - ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ) := by
    simp [signedDeficiency, Finset.sum_sub_distrib,
      SimpleGraph.card_neighborFinset_eq_degree, mul_comm]
  rw [hSum]
  change ((zeroCodegreeGraph G).degree v : ℤ) =
    1 + q * ((q : ℤ) + 1 - G.degree v) +
      (((q : ℤ) + 1) * G.degree v - ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ))
  simp only [signedDeficiency] at hEq
  push_cast at hEq
  nlinarith [hEq]

/-- Summing weights over all neighborhoods counts each weight by its vertex degree. -/
theorem sum_neighbor_weights {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n → ℤ) :
    (∑ v, ∑ w ∈ G.neighborFinset v, a w) = ∑ v, (G.degree v : ℤ) * a v := by
  classical
  simp_rw [G.neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter]
  have hFilter : (Finset.univ.filter fun w => G.Adj w v) = G.neighborFinset v := by
    ext w
    simp [G.neighborFinset_eq_filter, SimpleGraph.adj_comm]
  rw [hFilter]
  simp [SimpleGraph.card_neighborFinset_eq_degree]

/-- Ordered zero-codegree pairs satisfy the global deficiency-moment identity. -/
theorem zeroCodegree_degree_sum (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G) :
    (∑ v, ((zeroCodegreeGraph G).degree v : ℤ)) =
      ((q ^ 2 + q + 2 : ℕ) : ℤ) + 2 * q * (∑ v, signedDeficiency q G v) -
        ∑ v, signedDeficiency q G v * (signedDeficiency q G v - 1) := by
  have hRows : (∑ v, ((zeroCodegreeGraph G).degree v : ℤ)) =
      ((q ^ 2 + q + 2 : ℕ) : ℤ) + q * (∑ v, signedDeficiency q G v) +
        ∑ v, ∑ w ∈ G.neighborFinset v, signedDeficiency q G w := by
    simp_rw [zeroCodegree_degree_identity q G hFree]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [sum_neighbor_weights] at hRows
  have hTerm (v) : (G.degree v : ℤ) * signedDeficiency q G v =
      q * signedDeficiency q G v - signedDeficiency q G v * (signedDeficiency q G v - 1) := by
    unfold signedDeficiency
    ring
  simp_rw [hTerm] at hRows
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hRows
  linarith

/-- Density bounds the total signed deficiency with an explicit constant. -/
theorem dense_total_deficiency_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    (∑ v, signedDeficiency q G v) ≤ 2 * (q : ℤ) - 4 := by
  have hSum := sum_signedDeficiency q G
  rw [edgeSet_ncard] at hSum
  have hDenseInt : (q : ℤ) * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card := by
    exact_mod_cast hDense
  push_cast at hSum
  nlinarith [hDenseInt]

/-- The second signed-deficiency moment is quadratically bounded. -/
theorem dense_deficiency_square_sum_le (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    (∑ v, signedDeficiency q G v ^ 2) ≤ 5 * (q : ℤ) ^ 2 := by
  have hMoment := zeroCodegree_degree_sum q G hFree
  have hTotal := dense_total_deficiency_le q G hDense
  have hTerm (v) : signedDeficiency q G v * (signedDeficiency q G v - 1) =
      signedDeficiency q G v ^ 2 - signedDeficiency q G v := by ring
  simp_rw [hTerm] at hMoment
  rw [Finset.sum_sub_distrib] at hMoment
  have hZero : 0 ≤ ∑ v, ((zeroCodegreeGraph G).degree v : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hCoefficient : 0 ≤ 2 * (q : ℤ) + 1 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hTotal hCoefficient
  have hqInt : (2 : ℤ) ≤ q := by exact_mod_cast hq
  push_cast at hMoment
  nlinarith [hMoment, hScaled]

/-- An integer and its predecessor have nonnegative product. -/
theorem int_mul_pred_nonnegative (z : ℤ) : 0 ≤ z * (z - 1) := by
  by_cases h : 1 ≤ z
  · exact mul_nonneg (by omega) (by omega)
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- The total deficiency has a lower bound of the same linear scale. -/
theorem total_deficiency_lower (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G) :
    -(q : ℤ) ≤ ∑ v, signedDeficiency q G v := by
  have hMoment := zeroCodegree_degree_sum q G hFree
  have hZero : 0 ≤ ∑ v, ((zeroCodegreeGraph G).degree v : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hPred : 0 ≤ ∑ v, signedDeficiency q G v * (signedDeficiency q G v - 1) :=
    Finset.sum_nonneg (fun v _ => int_mul_pred_nonnegative (signedDeficiency q G v))
  have hqInt : (2 : ℤ) ≤ q := by exact_mod_cast hq
  push_cast at hMoment
  have hPositive : 0 ≤ (q : ℤ) ^ 2 + q + 2 + 2 * q * (∑ v, signedDeficiency q G v) := by
    nlinarith [hMoment]
  have hOrder : (q : ℤ) ^ 2 + q + 2 ≤ 2 * (q : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℤ) - 2)]
  by_contra h
  have hNegative : (∑ v, signedDeficiency q G v) < -(q : ℤ) := lt_of_not_ge h
  have hScaled := mul_lt_mul_of_pos_left hNegative (show 0 < 2 * (q : ℤ) by omega)
  nlinarith [hScaled]

/-- The number of ordered zero-codegree pairs has a quadratic upper bound. -/
theorem dense_zeroCodegree_count_le (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    (∑ v, ((zeroCodegreeGraph G).degree v : ℤ)) ≤ 6 * (q : ℤ) ^ 2 := by
  have hMoment := zeroCodegree_degree_sum q G hFree
  have hTotal := dense_total_deficiency_le q G hDense
  have hPred : 0 ≤ ∑ v, signedDeficiency q G v * (signedDeficiency q G v - 1) :=
    Finset.sum_nonneg (fun v _ => int_mul_pred_nonnegative (signedDeficiency q G v))
  have hqInt : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hTotal' : (∑ v, signedDeficiency q G v) ≤ 2 * (q : ℤ) := by omega
  have hScaled := mul_le_mul_of_nonneg_left hTotal' (show 0 ≤ 2 * (q : ℤ) by positivity)
  push_cast at hMoment
  nlinarith [hMoment, hScaled, sq_nonneg ((q : ℤ) - 2)]

/-- The squared total deficiency has a uniform quadratic bound. -/
theorem dense_total_deficiency_square_le (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    (∑ v, signedDeficiency q G v) ^ 2 ≤ 4 * (q : ℤ) ^ 2 := by
  have hLower := total_deficiency_lower q hq G hFree
  have hUpper := dense_total_deficiency_le q G hDense
  have hProduct : 0 ≤
      (2 * (q : ℤ) - ∑ v, signedDeficiency q G v) *
        (2 * (q : ℤ) + ∑ v, signedDeficiency q G v) :=
    mul_nonneg (by omega) (by omega)
  nlinarith [hProduct]

/-- Replace the original vertex by two adjacent vertices with prescribed neighborhoods. -/
def splitGraph {V : Type*} (G : SimpleGraph V) (u : V)
    (left right : Set V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | none, none => False
    | none, some y => y = u ∨ y ∈ right
    | some x, none => x = u ∨ x ∈ right
    | some x, some y => G.Adj x y ∧ (x = u → y ∈ left) ∧ (y = u → x ∈ left)
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact G.ne_of_adj h.1 rfl⟩

/-- A cycle using only original vertices would already be present before splitting. -/
theorem splitGraph_no_old_four_cycle {V : Type*} (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G) (u : V) (left right : Set V)
    (a b c d : V) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : (splitGraph G u left right).Adj (some a) (some b))
    (hbc : (splitGraph G u left right).Adj (some b) (some c))
    (hcd : (splitGraph G u left right).Adj (some c) (some d))
    (hda : (splitGraph G u left right).Adj (some d) (some a)) : False := by
  exact hFree (contains_four_cycle G a b c d hac hbd hab.1 hbc.1 hcd.1 hda.1)

/-- Each cycle through the new vertex has the two split vertices opposite. -/
theorem splitGraph_cycle_classification {V : Type*} (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G) (u : V) (left right : Set V)
    (hLeft : ∀ x ∈ left, G.Adj u x)
    (hRight : ∀ x ∈ right, G.Adj u x)
    (hIndependent : ∀ x y, G.Adj u x → G.Adj u y → ¬ G.Adj x y)
    (a b c : V) (hac : a ≠ c)
    (hna : (splitGraph G u left right).Adj none (some a))
    (hab : (splitGraph G u left right).Adj (some a) (some b))
    (hbc : (splitGraph G u left right).Adj (some b) (some c))
    (hcn : (splitGraph G u left right).Adj (some c) none) :
    b = u ∧ a ∈ left ∩ right ∧ c ∈ left ∩ right := by
  change a = u ∨ a ∈ right at hna
  change c = u ∨ c ∈ right at hcn
  change G.Adj a b ∧ (a = u → b ∈ left) ∧ (b = u → a ∈ left) at hab
  change G.Adj b c ∧ (b = u → c ∈ left) ∧ (c = u → b ∈ left) at hbc
  have ha : a ≠ u := by
    intro hau
    subst a
    rcases hcn with hcu | hcRight
    · exact hac hcu.symm
    · exact hIndependent b c (hLeft b (hab.2.1 rfl)) (hRight c hcRight) hbc.1
  have haRight : a ∈ right := hna.resolve_left ha
  have hc : c ≠ u := by
    intro hcu
    subst c
    exact hIndependent a b (hRight a haRight) (hLeft b (hbc.2.2 rfl)) hab.1
  have hcRight : c ∈ right := hcn.resolve_left hc
  have hb : b = u := by
    by_contra hbu
    have heq : a = c := common_neighbor_unique G hFree (Ne.symm hbu)
      (hRight a haRight) hab.1.symm (hRight c hcRight) hbc.1
    exact hac heq
  exact ⟨hb, ⟨hab.2.2 hb, haRight⟩, ⟨hbc.2.1 hb, hcRight⟩⟩

/-- Keeping the full old neighborhood preserves every old adjacency. -/
theorem splitGraph_full_adj_some {V : Type*} (G : SimpleGraph V)
    (u : V) (right : Set V) (v w : V) :
    (splitGraph G u (G.neighborSet u) right).Adj (some v) (some w) ↔ G.Adj v w := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_, ?_⟩
    · intro hv
      change G.Adj u w
      simpa only [hv] using h
    · intro hw
      change G.Adj u v
      simpa only [hw] using h.symm

/-- The new vertex has precisely the chosen neighbors and the old split vertex. -/
theorem splitGraph_neighborFinset_none {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) (right : Finset V) :
    (splitGraph G u (G.neighborSet u) right).neighborFinset none =
      (insert u right).image some := by
  classical
  ext x
  rw [SimpleGraph.mem_neighborFinset]
  cases x <;> simp [splitGraph, eq_comm]

/-- The original vertices receive one extra edge exactly at the prescribed set. -/
theorem splitGraph_neighborFinset_some {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) (right : Finset V) (v : V) :
    (splitGraph G u (G.neighborSet u) right).neighborFinset (some v) =
      (G.neighborFinset v).image some ∪
        (if v = u ∨ v ∈ right then {none} else ∅) := by
  classical
  ext x
  rw [SimpleGraph.mem_neighborFinset]
  cases x with
  | none => split_ifs <;> simp_all [splitGraph]
  | some w => split_ifs <;> simp [SimpleGraph.mem_neighborFinset, splitGraph_full_adj_some]

/-- Exact degree of the appended split vertex. -/
theorem splitGraph_degree_none {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) (right : Finset V)
    (hRight : ∀ x ∈ right, G.Adj u x) :
    (splitGraph G u (G.neighborSet u) right).degree none = right.card + 1 := by
  classical
  have hu : u ∉ right := fun h => G.ne_of_adj (hRight u h) rfl
  rw [← SimpleGraph.card_neighborFinset_eq_degree, splitGraph_neighborFinset_none,
    Finset.card_image_of_injective _ (Option.some_injective V), Finset.card_insert_of_notMem hu]

/-- Exact degree increment at every original vertex. -/
theorem splitGraph_degree_some {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) (right : Finset V) (v : V) :
    (splitGraph G u (G.neighborSet u) right).degree (some v) =
      G.degree v + if v = u ∨ v ∈ right then 1 else 0 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, splitGraph_neighborFinset_some]
  have hd : Disjoint ((G.neighborFinset v).image some)
      (if v = u ∨ v ∈ right then {none} else ∅) := by
    split_ifs <;> simp
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (Option.some_injective V)]
  split_ifs <;> simp

/-- The construction has exactly r+1 more edges than the original graph. -/
theorem splitGraph_edge_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) (right : Finset V)
    (hRight : ∀ x ∈ right, G.Adj u x) :
    (splitGraph G u (G.neighborSet u) right).edgeFinset.card =
      G.edgeFinset.card + right.card + 1 := by
  classical
  have hu : u ∉ right := fun h => G.ne_of_adj (hRight u h) rfl
  have hs : (∑ v : V, if v = u ∨ v ∈ right then (1 : ℕ) else 0) =
      right.card + 1 := by
    calc
      _ = (∑ v ∈ insert u right, (1 : ℕ)) := by
        rw [← Finset.sum_filter]
        congr 1
        ext v
        simp
      _ = right.card + 1 := by simp [hu]
  have hDeg := (splitGraph G u (G.neighborSet u) right).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, splitGraph_degree_none G u right hRight] at hDeg
  simp_rw [splitGraph_degree_some] at hDeg
  rw [Finset.sum_add_distrib, hs, G.sum_degrees_eq_twice_card_edges] at hDeg
  omega

/-- Overlap of size at most one produces no four-cycle at all. -/
theorem splitGraph_free_single_overlap {V : Type*} (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G) (u : V) (right : Set V)
    (hRight : ∀ x ∈ right, G.Adj u x)
    (hIndependent : ∀ x y, G.Adj u x → G.Adj u y → ¬ G.Adj x y)
    (hSubsingleton : right.Subsingleton) :
    (cycleGraph 4).Free (splitGraph G u (G.neighborSet u) right) := by
  let S := splitGraph G u (G.neighborSet u) right
  have hNoStart : ∀ x y z : Option V, x ≠ z → y ≠ none →
      S.Adj none x → S.Adj x y → S.Adj y z → S.Adj z none → False := by
    intro x y z hxz hy hnx hxy hyz hzn
    cases x with
    | none => exact hnx
    | some x =>
      cases y with
      | none => exact hy rfl
      | some y =>
        cases z with
        | none => exact hzn
        | some z =>
          obtain ⟨_, hx, hz⟩ := splitGraph_cycle_classification G hFree u
            (G.neighborSet u) right (fun _ h => h) hRight hIndependent x y z
            (by simpa using hxz) hnx hxy hyz hzn
          exact hxz (congrArg some (hSubsingleton hx.2 hz.2))
  apply (free_iff_common_neighbor_unique _).2
  intro x y hxy a b hxa hya hxb hyb
  by_contra hab
  cases x with
  | none => exact hNoStart a y b hab (Ne.symm hxy) hxa hya.symm hyb hxb.symm
  | some x =>
    cases y with
    | none => exact hNoStart a (some x) b hab (by simp) hya hxa.symm hxb hyb.symm
    | some y =>
      cases a with
      | none =>
        exact hNoStart (some x) b (some y) hxy (Ne.symm hab)
          hxa.symm hxb hyb.symm hya
      | some a =>
        cases b with
        | none =>
          exact hNoStart (some x) (some a) (some y) hxy (by simp)
            hxb.symm hxa hya.symm hyb
        | some b =>
          apply hab
          apply congrArg some
          exact common_neighbor_unique G hFree (by simpa using hxy)
            (splitGraph_full_adj_some G u right x a |>.mp hxa)
            (splitGraph_full_adj_some G u right y a |>.mp hya)
            (splitGraph_full_adj_some G u right x b |>.mp hxb)
            (splitGraph_full_adj_some G u right y b |>.mp hyb)

/-- Every four-cycle created by a split contains the appended vertex. -/
theorem splitGraph_copy_hits_new {V : Type*} (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G) (u : V) (left right : Set V)
    (f : (cycleGraph 4).Copy (splitGraph G u left right)) :
    ∃ i, f i = none := by
  classical
  by_contra hHit
  have hSome (i : Fin 4) : ∃ v, f i = some v := by
    cases hfi : f i with
    | none => exact False.elim (hHit ⟨i, hfi⟩)
    | some v => exact ⟨v, rfl⟩
  let g : Fin 4 → V := fun i => (hSome i).choose
  have hg (i : Fin 4) : f i = some (g i) := (hSome i).choose_spec
  apply hFree
  refine ⟨{ toHom := { toFun := g, map_rel' := ?_ }, injective' := ?_ }⟩
  · intro i j hij
    have hf := f.toHom.map_rel' hij
    change (splitGraph G u left right).Adj (f i) (f j) at hf
    rw [hg i, hg j] at hf
    exact hf.1
  · intro i j hij
    change g i = g j at hij
    apply f.injective
    change f i = f j
    rw [hg i, hg j, hij]

/-- Cyclic reindexing preserves an ordinary labelled four-cycle. -/
def rotateFourCopy {V : Type*} {G : SimpleGraph V}
    (f : (cycleGraph 4).Copy G) (i : Fin 4) : (cycleGraph 4).Copy G where
  toHom := {
    toFun := fun j => f (i + j)
    map_rel' := by
      intro j k hjk
      apply f.toHom.map_rel'
      have hRotation : ∀ i j k : Fin 4,
          (cycleGraph 4).Adj j k → (cycleGraph 4).Adj (i + j) (i + k) := by decide
      exact hRotation i j k hjk }
  injective' := by
    intro j k hjk
    exact add_left_cancel (f.injective hjk)

/-- With the appended vertex first, the opposite vertex and both remaining vertices are fixed. -/
theorem splitGraph_copy_normal_form {V : Type*} (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G) (u : V) (right : Set V)
    (hRight : ∀ x ∈ right, G.Adj u x)
    (hIndependent : ∀ x y, G.Adj u x → G.Adj u y → ¬ G.Adj x y)
    (f : (cycleGraph 4).Copy (splitGraph G u (G.neighborSet u) right))
    (hf : f 0 = none) :
    ∃ a ∈ right, ∃ b ∈ right,
      (fun i => f i) = ![none, some a, some u, some b] := by
  have hSome (i : Fin 4) (hi : i ≠ 0) : ∃ v, f i = some v := by
    cases hfi : f i with
    | none => exact False.elim (hi (f.injective (hfi.trans hf.symm)))
    | some v => exact ⟨v, rfl⟩
  obtain ⟨a, ha⟩ := hSome 1 (by decide)
  obtain ⟨v, hv⟩ := hSome 2 (by decide)
  obtain ⟨b, hb⟩ := hSome 3 (by decide)
  have h01 : (splitGraph G u (G.neighborSet u) right).Adj (f 0) (f 1) :=
    f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 0 1)
  have h12 : (splitGraph G u (G.neighborSet u) right).Adj (f 1) (f 2) :=
    f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 1 2)
  have h23 : (splitGraph G u (G.neighborSet u) right).Adj (f 2) (f 3) :=
    f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 2 3)
  have h30 : (splitGraph G u (G.neighborSet u) right).Adj (f 3) (f 0) :=
    f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 3 0)
  rw [hf, ha] at h01
  rw [ha, hv] at h12
  rw [hv, hb] at h23
  rw [hb, hf] at h30
  have hab : a ≠ b := by
    intro heq
    have : (1 : Fin 4) = 3 := f.injective (by
      change f 1 = f 3
      rw [ha, hb, heq])
    exact (by decide : (1 : Fin 4) ≠ 3) this
  obtain ⟨hvu, haRight, hbRight⟩ := splitGraph_cycle_classification G hFree u
    (G.neighborSet u) right (fun _ h => h) hRight hIndependent a v b hab h01 h12 h23 h30
  refine ⟨a, haRight.2, b, hbRight.2, ?_⟩
  funext i
  fin_cases i <;> simp [hf, ha, hv, hb, hvu]

/-- A labelled cycle in the split graph is determined by a rotation and two overlap vertices. -/
theorem splitGraph_copy_parameters {V : Type*} (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G) (u : V) (right : Set V)
    (hRight : ∀ x ∈ right, G.Adj u x)
    (hIndependent : ∀ x y, G.Adj u x → G.Adj u y → ¬ G.Adj x y)
    (f : (cycleGraph 4).Copy (splitGraph G u (G.neighborSet u) right)) :
    ∃ i : Fin 4, ∃ a ∈ right, ∃ b ∈ right,
      (fun j => f j) = fun j => ![none, some a, some u, some b] (j - i) := by
  obtain ⟨i, hi⟩ := splitGraph_copy_hits_new G hFree u (G.neighborSet u) right f
  have hRot : rotateFourCopy f i 0 = none := by
    change f (i + 0) = none
    simpa using hi
  obtain ⟨a, ha, b, hb, hForm⟩ := splitGraph_copy_normal_form G hFree u right
    hRight hIndependent (rotateFourCopy f i) hRot
  refine ⟨i, a, ha, b, hb, ?_⟩
  funext j
  have hj := congrFun hForm (j - i)
  change f (i + (j - i)) = _ at hj
  rw [add_comm i, sub_add_cancel] at hj
  exact hj

/-- A uniform quadratic upper bound suffices for the asymptotic split construction. -/
theorem splitGraph_copyCount_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hFree : (cycleGraph 4).Free G) (u : V) (right : Finset V)
    (hRight : ∀ x ∈ right, G.Adj u x)
    (hIndependent : ∀ x y, G.Adj u x → G.Adj u y → ¬ G.Adj x y) :
    (splitGraph G u (G.neighborSet u) right).copyCount (cycleGraph 4) ≤
      4 * right.card ^ 2 := by
  classical
  let S := splitGraph G u (G.neighborSet u) right
  let parameters : Finset (Fin 4 × V × V) := Finset.univ.product (right.product right)
  let forms : Finset (Fin 4 → Option V) :=
    parameters.image (fun p j => ![none, some p.2.1, some u, some p.2.2] (j - p.1))
  have hf (f : (cycleGraph 4).Copy S) : (fun j => f j) ∈ forms := by
    obtain ⟨i, a, ha, b, hb, hForm⟩ := splitGraph_copy_parameters G hFree u right
      hRight hIndependent f
    apply Finset.mem_image.mpr
    exact ⟨(i, a, b), Finset.mem_product.mpr
      ⟨Finset.mem_univ i, Finset.mem_product.mpr ⟨ha, hb⟩⟩, hForm.symm⟩
  have hCopies : (Finset.univ : Finset ((cycleGraph 4).Copy S)).card ≤ forms.card := by
    apply Finset.card_le_card_of_injOn (fun f : (cycleGraph 4).Copy S => fun j => f j)
    · exact fun f _ => hf f
    · intro f _ g _ hfg
      apply SimpleGraph.Copy.ext
      exact congrFun hfg
  calc
    S.copyCount (cycleGraph 4) =
        ((Finset.univ : Finset ((cycleGraph 4).Copy S)).image
          SimpleGraph.Copy.toSubgraph).card :=
      SimpleGraph.copyCount_eq_card_image_copyToSubgraph
    _ ≤ (Finset.univ : Finset ((cycleGraph 4).Copy S)).card := Finset.card_image_le
    _ ≤ forms.card := hCopies
    _ ≤ parameters.card := Finset.card_image_le
    _ = 4 * right.card ^ 2 := by simp [parameters, pow_two]

/-- The neighbors of an absolute point of a polarity are independent. -/
theorem polarity_absolute_neighborhood_independent {P L : Type*} [Membership P L]
    [Configuration.Nondegenerate P L] (π : Erdos60.Geometry.Polarity (P := P) (L := L))
    (u : P) (hu : π.Absolute u) :
    ∀ x y, π.graph.Adj u x → π.graph.Adj u y → ¬ π.graph.Adj x y := by
  intro x y hux huy hxy
  have hyu := (π.reciprocal u y).mp huy.2
  have hyx := (π.reciprocal x y).mp hxy.2
  rcases Configuration.Nondegenerate.eq_or_eq hu hyu hux.2 hyx with h | h
  · exact huy.ne h
  · exact hux.ne (π.line.injective h)

/-- The point type of each binary projective plane is finite. -/
noncomputable abbrev binaryPointFintype (k : ℕ) :
    Fintype (Erdos60.Construction.Point (GaloisField 2 k)) := Fintype.ofFinite _

/-- A binary projective plane supplies the exact base graph and a splittable vertex. -/
theorem exists_binary_base_graph (k : ℕ) (hk : k ≠ 0) :
    letI : Fintype (Erdos60.Construction.Point (GaloisField 2 k)) := binaryPointFintype k
    let q := 2 ^ k
    ∃ (G : SimpleGraph (Erdos60.Construction.Point (GaloisField 2 k)))
      (u : Erdos60.Construction.Point (GaloisField 2 k)),
      (cycleGraph 4).Free G ∧
      Fintype.card (Erdos60.Construction.Point (GaloisField 2 k)) = q ^ 2 + q + 1 ∧
      G.edgeFinset.card = q * (q + 1) ^ 2 / 2 ∧
      G.degree u = q ∧
      ∀ x y, G.Adj u x → G.Adj u y → ¬ G.Adj x y := by
  classical
  let : Fintype (Erdos60.Construction.Point (GaloisField 2 k)) := binaryPointFintype k
  dsimp only
  obtain ⟨π, hOrder, hAbsolute, _⟩ := Erdos60.Construction.power_two_construction k hk
  change Nat.card {u // π.Absolute u} = 2 ^ k + 1 at hAbsolute
  have hNonempty : Nonempty {u // π.Absolute u} :=
    (Nat.card_pos_iff.mp (by rw [hAbsolute]; omega)).1
  obtain ⟨⟨u, hu⟩⟩ := hNonempty
  have hFree : (cycleGraph 4).Free π.graph := by
    apply (free_iff_common_neighbor_unique _).2
    intro x y hxy a b hxa hya hxb hyb
    exact π.common_neighbor_unique hxy hxa hya hxb hyb
  have hVertices := π.card_vertices
  rw [hOrder] at hVertices
  have hSum := π.twice_edges_add_absolute
  rw [hOrder, hAbsolute] at hSum
  have hEdges : π.graph.edgeFinset.card = 2 ^ k * (2 ^ k + 1) ^ 2 / 2 := by
    have hDouble : 2 * π.graph.edgeFinset.card = 2 ^ k * (2 ^ k + 1) ^ 2 := by
      nlinarith [hSum]
    omega
  have hDegree := π.degree_add_diagonal u
  rw [Configuration.ProjectivePlane.pointCount_eq, hOrder, ite_eq_left hu] at hDegree
  refine ⟨π.graph, u, hFree, hVertices, hEdges, ?_, ?_⟩
  · omega
  · exact polarity_absolute_neighborhood_independent π u hu

/-- Relabel the split construction on the vertex type used by the exact target. -/
theorem exists_binary_split_graph (k r : ℕ) (hk : k ≠ 0) (hr : r ≤ 2 ^ k) :
    let q := 2 ^ k
    ∃ H : SimpleGraph (Fin (q ^ 2 + q + 2)),
      H.edgeFinset.card = q * (q + 1) ^ 2 / 2 + r + 1 ∧
      fourCycleCopies H ≤ 4 * r ^ 2 ∧
      (r ≤ 1 → (cycleGraph 4).Free H) := by
  classical
  dsimp only
  let : Fintype (Erdos60.Construction.Point (GaloisField 2 k)) := binaryPointFintype k
  obtain ⟨G, u, hFree, hVertices, hEdges, hDegree, hIndependent⟩ :=
    exists_binary_base_graph k hk
  have hr' : r ≤ (G.neighborFinset u).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hDegree]
    exact hr
  obtain ⟨R, hR, hCard⟩ := Finset.exists_subset_card_eq hr'
  have hRight : ∀ x ∈ R, G.Adj u x := by
    intro x hx
    exact (SimpleGraph.mem_neighborFinset G u x).mp (hR hx)
  let S := splitGraph G u (G.neighborSet u) R
  have hSize : Fintype.card (Option (Erdos60.Construction.Point (GaloisField 2 k))) =
      (2 ^ k) ^ 2 + 2 ^ k + 2 := by
    rw [Fintype.card_option, hVertices]
  let H := S.overFin hSize
  have hIso := S.overFinIso hSize
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [← hIso.card_edgeFinset_eq]
    change (splitGraph G u (G.neighborSet u) R).edgeFinset.card = _
    rw [splitGraph_edge_count G u R hRight, hEdges, hCard]
  · rw [fourCycleCopies_eq_copyCount, ← copyCount_iso hIso (cycleGraph 4)]
    exact (splitGraph_copyCount_le G hFree u R hRight hIndependent).trans_eq
      (by rw [hCard])
  · intro hrOne
    have hSingleton := Finset.card_le_one.mp (show R.card ≤ 1 by omega)
    have hSplitFree := splitGraph_free_single_overlap G hFree u R hRight
      hIndependent hSingleton
    exact (SimpleGraph.free_congr (SimpleGraph.Iso.refl : cycleGraph 4 ≃g cycleGraph 4)
      hIso).mp hSplitFree

/-- The actual extremal number at the above-plane order exceeds the base count by two. -/
theorem above_plane_extremal_lower (k : ℕ) (hk : k ≠ 0) :
    let q := 2 ^ k
    q * (q + 1) ^ 2 / 2 + 2 ≤ extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) := by
  classical
  dsimp only
  have hOne : 1 ≤ 2 ^ k := by
    have hPositive : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
    omega
  obtain ⟨H, hEdges, _, hFree⟩ := exists_binary_split_graph k 1 hk hOne
  have hBound := SimpleGraph.card_edgeFinset_le_extremalNumber (hFree (by omega))
  simpa only [Fintype.card_fin, hEdges, Nat.add_assoc] using hBound

/-- The extremal excess is at least two throughout the binary construction sequence. -/
theorem abovePlaneExcess_lower (k : ℕ) (hk : k ≠ 0) :
    2 ≤ abovePlaneExcess (2 ^ k) := by
  have h := above_plane_extremal_lower k hk
  dsimp only at h
  unfold abovePlaneExcess planeEdgeCount
  omega

/-- A small excess produces a graph exactly one edge above the actual extremal number. -/
theorem split_witness_at_extremal_threshold (k : ℕ) (hk : k ≠ 0)
    (hExcess : abovePlaneExcess (2 ^ k) ≤ 2 ^ k) :
    let q := 2 ^ k
    ∃ H : SimpleGraph (Fin (q ^ 2 + q + 2)),
      H.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) + 1 ∧
      fourCycleCopies H ≤ 4 * abovePlaneExcess q ^ 2 := by
  classical
  dsimp only
  obtain ⟨H, hEdges, hCount, _⟩ :=
    exists_binary_split_graph k (abovePlaneExcess (2 ^ k)) hk hExcess
  have hLower := above_plane_extremal_lower k hk
  dsimp only at hLower
  refine ⟨H, ?_, hCount⟩
  unfold abovePlaneExcess planeEdgeCount at hEdges
  omega

/-- The first hard branch of the manuscript supplies the density required by the degree bound. -/
theorem extremal_density_of_excess (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hEdges : G.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4))
    (hExcess : 3 ≤ abovePlaneExcess q) :
    q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card := by
  have hTwice := twice_planeEdgeCount q
  unfold abovePlaneExcess at hExcess
  omega

/-- Restricted two-edge paths have distinct unordered endpoint pairs. -/
theorem sum_choose_neighbors_in_set_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (centers endpoints : Finset (Fin n)) :
    (∑ v ∈ centers, ((G.neighborFinset v ∩ endpoints).card).choose 2) ≤
      endpoints.card.choose 2 := by
  classical
  let pairs := centers.sigma fun v => (G.neighborFinset v ∩ endpoints).powersetCard 2
  have hMembership (p : Σ _ : Fin n, Finset (Fin n)) (hp : p ∈ pairs) :
      p.2 ⊆ G.neighborFinset p.1 ∩ endpoints ∧ p.2.card = 2 := by
    exact Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hp).2
  have hMaps : ∀ p ∈ pairs, p.2 ∈ endpoints.powersetCard 2 := by
    intro p hp
    obtain ⟨hSub, hCard⟩ := hMembership p hp
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hCard⟩
    intro x hx
    exact (Finset.mem_inter.mp (hSub hx)).2
  have hInjective : Set.InjOn (fun p : Σ _ : Fin n, Finset (Fin n) => p.2)
      (pairs : Set _) := by
    rintro ⟨v, P⟩ hp ⟨w, Q⟩ hq hPQ
    change P = Q at hPQ
    have hvw : v = w := by
      by_contra hvw
      obtain ⟨hP, hCard⟩ := hMembership ⟨v, P⟩ hp
      obtain ⟨hQ, _⟩ := hMembership ⟨w, Q⟩ hq
      obtain ⟨a, b, hab, hPair⟩ := Finset.card_eq_two.mp hCard
      change P = {a, b} at hPair
      have haP : a ∈ P := by rw [hPair]; simp
      have hbP : b ∈ P := by rw [hPair]; simp
      have haQ : a ∈ Q := hPQ ▸ haP
      have hbQ : b ∈ Q := hPQ ▸ hbP
      have hva : G.Adj v a := by
        exact (G.mem_neighborFinset v a).mp (Finset.mem_inter.mp (hP haP)).1
      have hvb : G.Adj v b := by
        exact (G.mem_neighborFinset v b).mp (Finset.mem_inter.mp (hP hbP)).1
      have hwa : G.Adj w a := by
        exact (G.mem_neighborFinset w a).mp (Finset.mem_inter.mp (hQ haQ)).1
      have hwb : G.Adj w b := by
        exact (G.mem_neighborFinset w b).mp (Finset.mem_inter.mp (hQ hbQ)).1
      exact hab (common_neighbor_unique G hFree hvw hva hwa hvb hwb)
    subst w
    exact congrArg (Sigma.mk v) hPQ
  calc
    _ = pairs.card := by simp [pairs, Finset.card_sigma, Finset.card_powersetCard]
    _ ≤ (endpoints.powersetCard 2).card :=
      Finset.card_le_card_of_injOn (fun p => p.2) hMaps hInjective
    _ = endpoints.card.choose 2 := Finset.card_powersetCard _ _

/-- Removing one neighborhood loses at most one neighbor at every other vertex. -/
theorem degree_le_outside_neighbors_add_one {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v w : Fin n) (hvw : w ≠ v) :
    G.degree w ≤ (G.neighborFinset w \ G.neighborFinset v).card + 1 := by
  classical
  have hIntersection : (G.neighborFinset w ∩ G.neighborFinset v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hwa := (G.mem_neighborFinset w a).mp (Finset.mem_inter.mp ha).1
    have hva := (G.mem_neighborFinset v a).mp (Finset.mem_inter.mp ha).2
    have hwb := (G.mem_neighborFinset w b).mp (Finset.mem_inter.mp hb).1
    have hvb := (G.mem_neighborFinset v b).mp (Finset.mem_inter.mp hb).2
    exact common_neighbor_unique G hFree hvw hwa hva hwb hvb
  have hCard := Finset.card_sdiff_add_card_inter (G.neighborFinset w) (G.neighborFinset v)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hCard
  omega

/-- The integer tangent bound for the binomial coefficient used in the degree estimate. -/
theorem choose_two_tangent (x q : ℕ) :
    ((q : ℝ) - 1) * x - (q : ℝ) * (q - 1) / 2 ≤ (x.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  by_cases h : q ≤ x
  · have hx : (q : ℝ) ≤ x := by exact_mod_cast h
    have hProduct : 0 ≤ ((x : ℝ) - q) * (x - q + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hxNat : x + 1 ≤ q := by omega
    have hx : (x : ℝ) + 1 ≤ q := by exact_mod_cast hxNat
    have hProduct : 0 ≤ ((x : ℝ) - q) * (x - q + 1) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith

/-- Counting restricted two-edge paths yields a polynomial constraint on each degree. -/
theorem dense_degree_polynomial (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (v : Fin (q ^ 2 + q + 2)) :
    0 ≤ (G.degree v : ℝ) ^ 2 - (2 * (q : ℝ) ^ 2 + 5) * G.degree v +
      2 * (q : ℝ) ^ 3 + 6 * (q : ℝ) ^ 2 - 8 * q + 12 := by
  classical
  let U := (Finset.univ : Finset (Fin (q ^ 2 + q + 2))).erase v
  let T := (Finset.univ : Finset (Fin (q ^ 2 + q + 2))) \ G.neighborFinset v
  let outside := fun w => G.neighborFinset w \ G.neighborFinset v
  have hIntersection (w) : G.neighborFinset w ∩ T = outside w := by
    ext x
    simp [T, outside]
  have hLocal (w) (hw : w ∈ U) : G.degree w ≤ (outside w).card + 1 := by
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    exact degree_le_outside_neighbors_add_one G hFree v w hwv
  have hDegrees : (∑ w ∈ U, G.degree w) + G.degree v = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ v)
  have hLocalSum : (∑ w ∈ U, G.degree w) ≤
      (∑ w ∈ U, (outside w).card) + U.card := by
    calc
      _ ≤ ∑ w ∈ U, ((outside w).card + 1) := Finset.sum_le_sum hLocal
      _ = _ := by simp [Finset.sum_add_distrib]
  have hU : U.card + 1 = q ^ 2 + q + 2 := by
    simp [U]
  have hT : T.card + G.degree v = q ^ 2 + q + 2 := by
    have hSub : G.neighborFinset v ⊆ Finset.univ := Finset.subset_univ _
    simpa [T, SimpleGraph.card_neighborFinset_eq_degree] using
      Finset.card_sdiff_add_card_eq_card hSub
  have hSize : q * (q + 1) ^ 2 + 6 ≤
      (∑ w ∈ U, (outside w).card) + U.card + G.degree v := by omega
  have hSizeReal : (q : ℝ) * (q + 1) ^ 2 + 6 ≤
      (∑ w ∈ U, ((outside w).card : ℝ)) + U.card + G.degree v := by
    exact_mod_cast hSize
  have hUReal : (U.card : ℝ) + 1 = (q : ℝ) ^ 2 + q + 2 := by exact_mod_cast hU
  have hTReal : (T.card : ℝ) + G.degree v = (q : ℝ) ^ 2 + q + 2 := by
    exact_mod_cast hT
  have hSum : (q : ℝ) ^ 3 + q ^ 2 + 5 - G.degree v ≤
      ∑ w ∈ U, ((outside w).card : ℝ) := by nlinarith [hSizeReal, hUReal]
  have hTangent : ((q : ℝ) - 1) * (∑ w ∈ U, ((outside w).card : ℝ)) -
      U.card * ((q : ℝ) * (q - 1) / 2) ≤
      ∑ w ∈ U, ((outside w).card.choose 2 : ℝ) := by
    have h := Finset.sum_le_sum (fun w (_ : w ∈ U) => choose_two_tangent (outside w).card q)
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul] using h
  have hCountNat := sum_choose_neighbors_in_set_le G hFree U T
  simp_rw [hIntersection] at hCountNat
  have hCount : (∑ w ∈ U, ((outside w).card.choose 2 : ℝ)) ≤ (T.card.choose 2 : ℝ) := by
    exact_mod_cast hCountNat
  rw [Nat.cast_choose_two] at hCount
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hScaled := mul_le_mul_of_nonneg_left hSum (show 0 ≤ (q : ℝ) - 1 by linarith)
  have hCombined := hTangent.trans hCount
  have hUEq : (U.card : ℝ) = (q : ℝ) ^ 2 + q + 1 := by linarith
  have hTEq : (T.card : ℝ) = (q : ℝ) ^ 2 + q + 2 - G.degree v := by linarith
  rw [hUEq, hTEq] at hCombined
  nlinarith [hCombined, hScaled]

/-- Dense four-cycle-free graphs at the above-plane order have maximum degree q+3. -/
theorem dense_degree_le (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (v : Fin (q ^ 2 + q + 2)) : G.degree v ≤ q + 3 := by
  have hPoly := dense_degree_polynomial q hq G hFree hDense v
  have hMax : G.degree v ≤ q ^ 2 + q + 1 := by
    have h := G.degree_lt_card_verts v
    simp only [Fintype.card_fin] at h
    omega
  by_contra hTooLarge
  have hMin : q + 4 ≤ G.degree v := by omega
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hMinReal : (q : ℝ) + 4 ≤ G.degree v := by exact_mod_cast hMin
  have hMaxReal : (G.degree v : ℝ) ≤ (q : ℝ) ^ 2 + q + 1 := by exact_mod_cast hMax
  have hProduct : ((G.degree v : ℝ) - (q + 4)) *
      (G.degree v - ((q : ℝ) ^ 2 + q + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hDrop : 0 ≤ (q : ℝ) * (q - 2) * (G.degree v - (q + 4)) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  nlinarith [hProduct, hDrop, sq_nonneg (q : ℝ)]

/-- Squared Euclidean norm of an integer vector. -/
def vectorSquareSum {n : ℕ} (x : Fin n → ℤ) : ℤ := ∑ v, x v ^ 2

theorem vectorSquareSum_nonnegative {n : ℕ} (x : Fin n → ℤ) :
    0 ≤ vectorSquareSum x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Symmetry identifies the adjacency energy with its second-walk quadratic form. -/
theorem adjMatrix_energy_identity {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℤ) :
    vectorSquareSum (G.adjMatrix ℤ *ᵥ x) =
      x ⬝ᵥ ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ x) := by
  have hTranspose : x ᵥ* G.adjMatrix ℤ = G.adjMatrix ℤ *ᵥ x := by
    rw [← Matrix.mulVec_transpose, G.transpose_adjMatrix]
  calc
    _ = (G.adjMatrix ℤ *ᵥ x) ⬝ᵥ (G.adjMatrix ℤ *ᵥ x) := by
      simp only [vectorSquareSum, dotProduct, pow_two]
    _ = (x ᵥ* G.adjMatrix ℤ) ⬝ᵥ (G.adjMatrix ℤ *ᵥ x) := by rw [hTranspose]
    _ = x ⬝ᵥ (G.adjMatrix ℤ *ᵥ (G.adjMatrix ℤ *ᵥ x)) :=
      (Matrix.dotProduct_mulVec _ _ _).symm
    _ = _ := by rw [Matrix.mulVec_mulVec]

theorem diagonal_quadratic_form {n : ℕ} (d x : Fin n → ℤ) :
    x ⬝ᵥ (Matrix.diagonal d *ᵥ x) = ∑ v, d v * x v ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem allOnes_quadratic_form {n : ℕ} (x : Fin n → ℤ) :
    x ⬝ᵥ (allOnesMatrix n *ᵥ x) = (∑ v, x v) ^ 2 := by
  have hOnes : allOnesMatrix n *ᵥ x = fun _ => ∑ v, x v := by
    ext v
    simp [allOnesMatrix, Matrix.mulVec, dotProduct]
  rw [hOnes]
  simp only [dotProduct, ← Finset.sum_mul, pow_two]

/-- Cauchy-Schwarz bounds the quadratic form of a zero-one adjacency matrix. -/
theorem adjMatrix_quadratic_square_le {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℤ) :
    (x ⬝ᵥ (G.adjMatrix ℤ *ᵥ x)) ^ 2 ≤
      (∑ v, (G.degree v : ℤ)) * vectorSquareSum x ^ 2 := by
  classical
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => G.adjMatrix ℤ p.1 p.2) (fun p => x p.1 * x p.2)
  have hForm : (∑ p : Fin n × Fin n, G.adjMatrix ℤ p.1 p.2 * (x p.1 * x p.2)) =
      x ⬝ᵥ (G.adjMatrix ℤ *ᵥ x) := by
    simp only [Fintype.sum_prod_type, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hEntries : (∑ p : Fin n × Fin n, (G.adjMatrix ℤ p.1 p.2) ^ 2) =
      ∑ v, (G.degree v : ℤ) := by
    have hIdempotent (i j) : (G.adjMatrix ℤ i j) ^ 2 = G.adjMatrix ℤ i j := by
      simp only [G.adjMatrix_apply]
      split_ifs <;> norm_num
    simp_rw [hIdempotent]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _
    have hRow : (G.adjMatrix ℤ *ᵥ (1 : Fin n → ℤ)) v = (G.degree v : ℤ) := by simp
    simpa [Matrix.mulVec, dotProduct] using hRow
  have hProducts : (∑ p : Fin n × Fin n, (x p.1 * x p.2) ^ 2) = vectorSquareSum x ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp only [vectorSquareSum, pow_two]
  simpa only [hForm, hEntries, hProducts] using hCauchy

/-- The adjacency energy splits into a diagonal part and a zero-codegree correction. -/
theorem adjMatrix_defect_energy (q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (x : Fin n → ℤ) :
    vectorSquareSum (G.adjMatrix ℤ *ᵥ x) =
      (∑ v, x v) ^ 2 + ∑ v, ((G.degree v : ℤ) - 1) * x v ^ 2 -
        x ⬝ᵥ ((zeroCodegreeGraph G).adjMatrix ℤ *ᵥ x) := by
  rw [adjMatrix_energy_identity, adjMatrix_square_defect_identity q G hFree,
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_add,
    diagonal_quadratic_form, allOnes_quadratic_form, diagonal_quadratic_form]
  have hDiagonal : (∑ v, (q : ℤ) * x v ^ 2) -
      (∑ v, signedDeficiency q G v * x v ^ 2) =
      ∑ v, ((G.degree v : ℤ) - 1) * x v ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    unfold signedDeficiency
    ring
  linarith

/-- The spectral estimate needed for the high-degree vertices, stated without division. -/
theorem dense_adjacency_energy_le (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (x : Fin (q ^ 2 + q + 2) → ℤ) (hZero : ∑ v, x v = 0) :
    vectorSquareSum (G.adjMatrix ℤ *ᵥ x) ≤ 5 * (q : ℤ) * vectorSquareSum x := by
  have hNorm := vectorSquareSum_nonnegative x
  have hCount := dense_zeroCodegree_count_le q hq G hFree hDense
  have hCauchy := adjMatrix_quadratic_square_le (zeroCodegreeGraph G) x
  have hSquare : (x ⬝ᵥ ((zeroCodegreeGraph G).adjMatrix ℤ *ᵥ x)) ^ 2 ≤
      (3 * (q : ℤ) * vectorSquareSum x) ^ 2 := by
    have hScaled := mul_le_mul_of_nonneg_right hCount (sq_nonneg (vectorSquareSum x))
    have hPositive : 0 ≤ (q : ℤ) ^ 2 * vectorSquareSum x ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith [hCauchy, hScaled]
  have hAbs := abs_le_of_sq_le_sq' hSquare
    (show 0 ≤ 3 * (q : ℤ) * vectorSquareSum x by positivity)
  have hDiagonal : (∑ v, ((G.degree v : ℤ) - 1) * x v ^ 2) ≤
      ((q : ℤ) + 2) * vectorSquareSum x := by
    calc
      _ ≤ ∑ v, ((q : ℤ) + 2) * x v ^ 2 := by
        apply Finset.sum_le_sum
        intro v _
        have hDegree : (G.degree v : ℤ) ≤ q + 3 := by
          exact_mod_cast dense_degree_le q hq G hFree hDense v
        exact mul_le_mul_of_nonneg_right (by omega) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hEnergy := adjMatrix_defect_energy q G hFree x
  rw [hZero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at hEnergy
  have hqInt : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hRemainder : 0 ≤ ((q : ℤ) - 2) * vectorSquareSum x :=
    mul_nonneg (by omega) hNorm
  nlinarith [hEnergy, hDiagonal, hAbs.1]

/-- An integral multiple of the centered deficiency vector. -/
def centeredDeficiency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : ℤ :=
  (n : ℤ) * signedDeficiency q G v - ∑ w, signedDeficiency q G w

theorem centeredDeficiency_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    (∑ v, centeredDeficiency q G v) = 0 := by
  simp [centeredDeficiency, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem centeredDeficiency_square_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    vectorSquareSum (centeredDeficiency q G) =
      (n : ℤ) ^ 2 * (∑ v, signedDeficiency q G v ^ 2) -
        n * (∑ v, signedDeficiency q G v) ^ 2 := by
  let F := ∑ v, signedDeficiency q G v
  have hTerm (v : Fin n) : centeredDeficiency q G v ^ 2 =
      (n : ℤ) ^ 2 * signedDeficiency q G v ^ 2 -
        (2 * n * F) * signedDeficiency q G v + F ^ 2 := by
    dsimp [centeredDeficiency, F]
    ring
  unfold vectorSquareSum
  simp_rw [hTerm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [F]
  ring

theorem dense_centeredDeficiency_square_sum_le (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    vectorSquareSum (centeredDeficiency q G) ≤
      ((q ^ 2 + q + 2 : ℕ) : ℤ) ^ 2 * (5 * (q : ℤ) ^ 2) := by
  rw [centeredDeficiency_square_sum]
  have hMoment := dense_deficiency_square_sum_le q hq G hFree hDense
  have hScaled := mul_le_mul_of_nonneg_left hMoment
    (sq_nonneg (((q ^ 2 + q + 2 : ℕ) : ℤ)))
  have hCorrection : 0 ≤ ((q ^ 2 + q + 2 : ℕ) : ℤ) *
      (∑ v, signedDeficiency q G v) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- The centered image has the cubic energy bound used to control high degrees. -/
theorem dense_centeredDeficiency_energy_le (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    vectorSquareSum (G.adjMatrix ℤ *ᵥ centeredDeficiency q G) ≤
      25 * ((q ^ 2 + q + 2 : ℕ) : ℤ) ^ 2 * (q : ℤ) ^ 3 := by
  calc
    _ ≤ 5 * (q : ℤ) * vectorSquareSum (centeredDeficiency q G) :=
      dense_adjacency_energy_le q hq G hFree hDense _ (centeredDeficiency_sum q G)
    _ ≤ 5 * (q : ℤ) * (((q ^ 2 + q + 2 : ℕ) : ℤ) ^ 2 * (5 * (q : ℤ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (dense_centeredDeficiency_square_sum_le q hq G hFree hDense)
        (by positivity)
    _ = _ := by ring

/-- The nonreturning two-edge paths from a vertex have distinct endpoints. -/
theorem sum_neighbor_degree_sub_one_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) :
    (∑ w ∈ G.neighborFinset v, (G.degree w - 1)) ≤ n - 1 := by
  classical
  let ends := fun w : Fin n => (G.neighborFinset w).erase v
  have hPair : (G.neighborFinset v : Set (Fin n)).PairwiseDisjoint ends := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hxz hyz
    have hxv : G.Adj x v := by simpa [SimpleGraph.adj_comm] using hx
    have hyv : G.Adj y v := by simpa [SimpleGraph.adj_comm] using hy
    have hxz' : G.Adj x z := by simpa [ends] using (Finset.mem_erase.mp hxz).2
    have hyz' : G.Adj y z := by simpa [ends] using (Finset.mem_erase.mp hyz).2
    have hvz : v = z := common_neighbor_unique G hFree hxy hxv hyv hxz' hyz'
    exact (Finset.mem_erase.mp hxz).1 hvz.symm
  have hSubset : (G.neighborFinset v).biUnion ends ⊆ Finset.univ.erase v := by
    intro z hz
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_univ z⟩
  have hEach : ∀ w ∈ G.neighborFinset v, (ends w).card = G.degree w - 1 := by
    intro w hw
    have hvw : v ∈ G.neighborFinset w := by simpa [SimpleGraph.adj_comm] using hw
    simp only [ends, Finset.card_erase_of_mem hvw, SimpleGraph.card_neighborFinset_eq_degree]
  calc
    (∑ w ∈ G.neighborFinset v, (G.degree w - 1)) =
        ∑ w ∈ G.neighborFinset v, (ends w).card := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (hEach w hw).symm
    _ = ((G.neighborFinset v).biUnion ends).card := (Finset.card_biUnion hPair).symm
    _ ≤ n - 1 := by simpa using Finset.card_le_card hSubset

/-- The two-path bound in degree-sum form. -/
theorem sum_neighbor_degrees_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) :
    (∑ w ∈ G.neighborFinset v, G.degree w) ≤ n - 1 + G.degree v := by
  classical
  have hPositive : ∀ w ∈ G.neighborFinset v, 1 ≤ G.degree w := by
    intro w hw
    have hAdjacent : G.Adj v w := by simpa using hw
    exact hAdjacent.degree_pos_right
  have hSum : (∑ w ∈ G.neighborFinset v, G.degree w) =
      (∑ w ∈ G.neighborFinset v, (G.degree w - 1)) + G.degree v := by
    calc
      _ = ∑ w ∈ G.neighborFinset v, ((G.degree w - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro w hw
        have := hPositive w hw
        omega
      _ = _ := by
        simp [Finset.sum_add_distrib, SimpleGraph.card_neighborFinset_eq_degree]
  rw [hSum]
  exact Nat.add_le_add_right (sum_neighbor_degree_sub_one_le G hFree v) _

/-- Exact lower bound on signed deficiency in a neighborhood. -/
theorem neighbor_signedDeficiency_lower {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G) (v : Fin n) :
    (q : ℤ) * G.degree v - ((n - 1 : ℕ) : ℤ) ≤
      ∑ w ∈ G.neighborFinset v, signedDeficiency q G w := by
  classical
  have hWalks := sum_neighbor_degrees_le G hFree v
  have hBound : (∑ w ∈ G.neighborFinset v, (G.degree w : ℤ)) ≤
      ((n - 1 : ℕ) : ℤ) + G.degree v := by
    exact_mod_cast hWalks
  have hSum : (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) =
      ((q : ℤ) + 1) * G.degree v -
        (∑ w ∈ G.neighborFinset v, (G.degree w : ℤ)) := by
    simp [signedDeficiency, Finset.sum_sub_distrib,
      SimpleGraph.card_neighborFinset_eq_degree, mul_comm]
  rw [hSum]
  nlinarith

/-- Applying the adjacency matrix to the integral centered vector. -/
theorem centeredDeficiency_image {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    (G.adjMatrix ℤ *ᵥ centeredDeficiency q G) v =
      (n : ℤ) * (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) -
        G.degree v * (∑ w, signedDeficiency q G w) := by
  rw [G.adjMatrix_mulVec_apply]
  simp [centeredDeficiency, Finset.sum_sub_distrib, ← Finset.mul_sum,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Every high vertex has a large coordinate in the centered adjacency image. -/
theorem high_vertex_centered_image_lower (q : ℕ) (hq : 8 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (v : Fin (q ^ 2 + q + 2)) (hHigh : q + 2 ≤ G.degree v) :
    (((q ^ 2 + q + 2 : ℕ) : ℤ) * q) ≤
      2 * (G.adjMatrix ℤ *ᵥ centeredDeficiency q G) v := by
  have hqInt : (8 : ℤ) ≤ q := by exact_mod_cast hq
  have hDegreeLower : (q : ℤ) + 2 ≤ G.degree v := by exact_mod_cast hHigh
  have hNeighbor := neighbor_signedDeficiency_lower q G hFree v
  have hOrder : (q ^ 2 + q + 2 : ℕ) - 1 = q ^ 2 + q + 1 := by omega
  rw [hOrder] at hNeighbor
  push_cast at hNeighbor
  have hDegreeScaled := mul_le_mul_of_nonneg_left hDegreeLower (Int.natCast_nonneg q)
  have hNeighborLower : (q : ℤ) - 1 ≤
      ∑ w ∈ G.neighborFinset v, signedDeficiency q G w := by
    nlinarith [hNeighbor, hDegreeScaled]
  have hNeighborScaled := mul_le_mul_of_nonneg_left hNeighborLower
    (show 0 ≤ ((q ^ 2 + q + 2 : ℕ) : ℤ) by positivity)
  have hTotal := dense_total_deficiency_le q G hDense
  have hTotal' : (∑ w, signedDeficiency q G w) ≤ 2 * (q : ℤ) := by omega
  have hDegreeUpper : (G.degree v : ℤ) ≤ (q : ℤ) + 3 := by
    exact_mod_cast dense_degree_le q (by omega) G hFree hDense v
  have hCorrection : (G.degree v : ℤ) * (∑ w, signedDeficiency q G w) ≤
      ((q : ℤ) + 3) * (2 * q) := by
    calc
      _ ≤ (G.degree v : ℤ) * (2 * q) :=
        mul_le_mul_of_nonneg_left hTotal' (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hDegreeUpper (by positivity)
  have hCubic : 0 ≤ (q : ℤ) ^ 3 - 5 * q ^ 2 - 12 * q - 4 := by
    have hA : 0 ≤ (q : ℤ) ^ 2 * (q - 8) := mul_nonneg (sq_nonneg _) (by omega)
    have hB : 0 ≤ (q : ℤ) * (q - 8) := mul_nonneg (by positivity) (by omega)
    nlinarith [hA, hB]
  rw [centeredDeficiency_image]
  push_cast at hNeighborScaled ⊢
  nlinarith [hNeighborScaled, hCorrection, hCubic]

/-- Vertices of degree at least q+2, prior to the final degree refinement. -/
def highVertices {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => q + 2 ≤ G.degree v

/-- The spectral estimate yields a linear bound on the number of high vertices. -/
theorem highVertices_card_le (q : ℕ) (hq : 8 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    (highVertices q G).card ≤ 100 * q := by
  classical
  let y := G.adjMatrix ℤ *ᵥ centeredDeficiency q G
  let N : ℤ := ((q ^ 2 + q + 2 : ℕ) : ℤ)
  have hEach (v) (hv : v ∈ highVertices q G) : (N * q) ^ 2 ≤ 4 * y v ^ 2 := by
    have hHigh := (Finset.mem_filter.mp hv).2
    have hLower := high_vertex_centered_image_lower q hq G hFree hDense v hHigh
    change N * q ≤ 2 * y v at hLower
    have hPositive : 0 ≤ N * q := by dsimp [N]; positivity
    have hRight : 0 ≤ 2 * y v := hPositive.trans hLower
    have hSquare := (sq_le_sq₀ hPositive hRight).2 hLower
    nlinarith [hSquare]
  have hSum : ((highVertices q G).card : ℤ) * (N * q) ^ 2 ≤
      4 * (∑ v ∈ highVertices q G, y v ^ 2) := by
    have h := Finset.sum_le_sum hEach
    simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] using h
  have hSubset : (∑ v ∈ highVertices q G, y v ^ 2) ≤ vectorSquareSum y := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro v _ _
    exact sq_nonneg _
  have hEnergy := dense_centeredDeficiency_energy_le q (by omega) G hFree hDense
  change vectorSquareSum y ≤ 25 * N ^ 2 * (q : ℤ) ^ 3 at hEnergy
  have hMain : ((highVertices q G).card : ℤ) * (N * q) ^ 2 ≤
      (100 * (q : ℤ)) * (N * q) ^ 2 := by
    calc
      _ ≤ 4 * (∑ v ∈ highVertices q G, y v ^ 2) := hSum
      _ ≤ 4 * vectorSquareSum y := mul_le_mul_of_nonneg_left hSubset (by norm_num)
      _ ≤ 4 * (25 * N ^ 2 * (q : ℤ) ^ 3) :=
        mul_le_mul_of_nonneg_left hEnergy (by norm_num)
      _ = _ := by ring
  have hScale : 0 < (N * q) ^ 2 := by
    dsimp [N]
    have hqInt : (8 : ℤ) ≤ q := by exact_mod_cast hq
    positivity
  have hCard := (mul_le_mul_iff_of_pos_right hScale).mp hMain
  exact_mod_cast hCard

/-- Positive part of a vertex's signed deficiency. -/
def positiveDeficiency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : ℤ :=
  max (signedDeficiency q G v) 0

theorem positiveDeficiency_nonnegative {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (v : Fin n) : 0 ≤ positiveDeficiency q G v := le_max_right _ _

theorem positiveDeficiency_le_signed_add_high {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (v : Fin n) (hDegree : G.degree v ≤ q + 3) :
    positiveDeficiency q G v ≤ signedDeficiency q G v +
      if q + 2 ≤ G.degree v then 2 else 0 := by
  have hUpper : (G.degree v : ℤ) ≤ (q : ℤ) + 3 := by exact_mod_cast hDegree
  by_cases hHigh : q + 2 ≤ G.degree v
  · have hLower : (q : ℤ) + 2 ≤ G.degree v := by exact_mod_cast hHigh
    have hNonpositive : (q : ℤ) + 1 - G.degree v ≤ 0 := by omega
    simp only [positiveDeficiency, signedDeficiency, max_eq_right hNonpositive,
      ite_eq_left hHigh]
    omega
  · have hLower : G.degree v ≤ q + 1 := by omega
    have hLowerInt : (G.degree v : ℤ) ≤ (q : ℤ) + 1 := by exact_mod_cast hLower
    have hNonnegative : 0 ≤ (q : ℤ) + 1 - G.degree v := by omega
    simp only [positiveDeficiency, signedDeficiency, max_eq_left hNonnegative,
      ite_eq_right hHigh, add_zero, le_refl]

theorem positiveDeficiency_sum_le_signed_add_high {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (hDegree : ∀ v, G.degree v ≤ q + 3) :
    (∑ v, positiveDeficiency q G v) ≤ (∑ v, signedDeficiency q G v) +
      2 * (highVertices q G).card := by
  have hPointwise (v) (_ : v ∈ Finset.univ) :=
    positiveDeficiency_le_signed_add_high q G v (hDegree v)
  have hSum := Finset.sum_le_sum hPointwise
  have hHighCount : (∑ v, if q + 2 ≤ G.degree v then (2 : ℤ) else 0) =
      2 * (highVertices q G).card := by
    rw [← Finset.sum_filter]
    simp [highVertices, mul_comm]
  rwa [Finset.sum_add_distrib, hHighCount] at hSum

/-- The total positive deficiency has an explicit linear bound. -/
theorem dense_positiveDeficiency_sum_le (q : ℕ) (hq : 8 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    (∑ v, positiveDeficiency q G v) ≤ 202 * (q : ℤ) := by
  have hSum := positiveDeficiency_sum_le_signed_add_high q G
    (dense_degree_le q (by omega) G hFree hDense)
  have hTotal := dense_total_deficiency_le q G hDense
  have hCard : ((highVertices q G).card : ℤ) ≤ 100 * (q : ℤ) := by
    exact_mod_cast highVertices_card_le q hq G hFree hDense
  omega

/-- Nonreturning neighborhoods of selected neighbors are pairwise disjoint. -/
theorem nonreturning_neighbor_weight_sum_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) (S : Finset (Fin n))
    (hS : S ⊆ G.neighborFinset v) (a : Fin n → ℤ) (ha : ∀ w, 0 ≤ a w) :
    (∑ w ∈ S, ∑ z ∈ (G.neighborFinset w).erase v, a z) ≤ ∑ z, a z := by
  classical
  let ends := fun w => (G.neighborFinset w).erase v
  have hDisjoint : (S : Set (Fin n)).PairwiseDisjoint ends := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hxz hyz
    have hxv : G.Adj x v := ((G.mem_neighborFinset v x).mp (hS hx)).symm
    have hyv : G.Adj y v := ((G.mem_neighborFinset v y).mp (hS hy)).symm
    have hxz' : G.Adj x z := (G.mem_neighborFinset x z).mp (Finset.mem_erase.mp hxz).2
    have hyz' : G.Adj y z := (G.mem_neighborFinset y z).mp (Finset.mem_erase.mp hyz).2
    have hvz := common_neighbor_unique G hFree hxy hxv hyv hxz' hyz'
    exact (Finset.mem_erase.mp hxz).1 hvz.symm
  calc
    _ = ∑ z ∈ S.biUnion ends, a z := (Finset.sum_biUnion hDisjoint).symm
    _ ≤ ∑ z, a z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z _ _
      exact ha z

/-- A minimum-degree ratio bounds each positive deficiency. -/
theorem positiveDeficiency_scaled_le {n : ℕ} (q C : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin n)) (v : Fin n) (hMin : q ≤ C * G.degree v) :
    (C : ℤ) * positiveDeficiency q G v ≤ C * ((q : ℤ) + 1) - q := by
  have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
  have hMinInt : (q : ℤ) ≤ C * (G.degree v : ℤ) := by exact_mod_cast hMin
  have hProduct : 0 ≤ ((C : ℤ) - 1) * q := mul_nonneg (by omega) (by positivity)
  by_cases hSign : 0 ≤ signedDeficiency q G v
  · unfold positiveDeficiency
    rw [max_eq_left hSign]
    unfold signedDeficiency
    nlinarith [hMinInt]
  · have hSign' : signedDeficiency q G v ≤ 0 := le_of_not_ge hSign
    simp only [positiveDeficiency, max_eq_right hSign', mul_zero]
    nlinarith [hProduct]

theorem high_vertex_positive_neighbor_sum (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hHigh : q + 2 ≤ G.degree v) :
    (q : ℤ) - 1 ≤ ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  have hNeighbor := neighbor_signedDeficiency_lower q G hFree v
  have hOrder : (q ^ 2 + q + 2 : ℕ) - 1 = q ^ 2 + q + 1 := by omega
  rw [hOrder] at hNeighbor
  push_cast at hNeighbor
  have hDegree : (q : ℤ) + 2 ≤ G.degree v := by exact_mod_cast hHigh
  have hScaled := mul_le_mul_of_nonneg_left hDegree (Int.natCast_nonneg q)
  have hSigned : (q : ℤ) - 1 ≤ ∑ w ∈ G.neighborFinset v, signedDeficiency q G w := by
    nlinarith [hNeighbor, hScaled]
  exact hSigned.trans (Finset.sum_le_sum (fun _ _ => le_max_left _ _))

/-- Each vertex has boundedly many high neighbors under a fixed minimum-degree ratio. -/
theorem high_neighbor_count_le (q C : ℕ) (hC : 1 ≤ C) (hq : 8 ≤ q) (hqC : 4 * C ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hMin : ∀ v, q ≤ C * G.degree v) (v : Fin (q ^ 2 + q + 2)) :
    (G.neighborFinset v ∩ highVertices q G).card ≤ 404 * C := by
  classical
  let S := G.neighborFinset v ∩ highVertices q G
  have hS : S ⊆ G.neighborFinset v := Finset.inter_subset_left
  have hDisjointBound := nonreturning_neighbor_weight_sum_le G hFree v S hS
    (positiveDeficiency q G) (positiveDeficiency_nonnegative q G)
  have hEach (w) (hw : w ∈ S) :
      (q : ℤ) - 1 - positiveDeficiency q G v ≤
        ∑ z ∈ (G.neighborFinset w).erase v, positiveDeficiency q G z := by
    have hwv : G.Adj w v := ((G.mem_neighborFinset v w).mp (hS hw)).symm
    have hvMem : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr hwv
    have hHigh : q + 2 ≤ G.degree w :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2
    have hLower := high_vertex_positive_neighbor_sum q G hFree w hHigh
    have hErase := Finset.sum_erase_add (G.neighborFinset w) (positiveDeficiency q G) hvMem
    linarith
  have hSummed := (Finset.sum_le_sum hEach).trans hDisjointBound
  simp only [Finset.sum_const, nsmul_eq_mul] at hSummed
  have hScaledWeight := positiveDeficiency_scaled_le q C hC G v (hMin v)
  have hTotal := dense_positiveDeficiency_sum_le q hq G hFree hDense
  have hStep : (q : ℤ) - 2 * C ≤ C * ((q : ℤ) - 1 - positiveDeficiency q G v) := by
    nlinarith [hScaledWeight]
  have hStepScaled := mul_le_mul_of_nonneg_left hStep (Int.natCast_nonneg S.card)
  have hSummedScaled := mul_le_mul_of_nonneg_left hSummed (Int.natCast_nonneg C)
  have hTotalScaled := mul_le_mul_of_nonneg_left hTotal (Int.natCast_nonneg C)
  have hBound : (S.card : ℤ) * (q - 2 * C) ≤ 202 * C * q := by
    nlinarith [hStepScaled, hSummedScaled, hTotalScaled]
  have hqCInt : 4 * (C : ℤ) ≤ q := by exact_mod_cast hqC
  have hGap : 0 ≤ (S.card : ℤ) * (q - 4 * C) := mul_nonneg (by positivity) (by omega)
  have hMain : (S.card : ℤ) * q ≤ (404 * (C : ℤ)) * q := by nlinarith [hBound, hGap]
  have hqPositive : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  have hCard := (mul_le_mul_iff_of_pos_right hqPositive).mp hMain
  exact_mod_cast hCard

/-- Double-count weights on the neighbors of a selected vertex set. -/
theorem sum_selected_neighbor_weights {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (a : Fin n → ℤ) :
    (∑ v ∈ S, ∑ w ∈ G.neighborFinset v, a w) =
      ∑ w, ((G.neighborFinset w ∩ S).card : ℤ) * a w := by
  classical
  calc
    _ = ∑ v ∈ S, ∑ w, if G.Adj v w then a w else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [G.neighborFinset_eq_filter, Finset.sum_filter]
    _ = ∑ w, ∑ v ∈ S, if G.Adj v w then a w else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_filter]
      have hFilter : (S.filter fun v => G.Adj v w) = G.neighborFinset w ∩ S := by
        ext v
        simp [G.neighborFinset_eq_filter, SimpleGraph.adj_comm, and_comm]
      rw [hFilter]
      simp

/-- The number of high vertices is bounded solely by the minimum-degree ratio. -/
theorem highVertices_card_constant_le (q C : ℕ) (hC : 1 ≤ C) (hq : 8 ≤ q) (hqC : 4 * C ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hMin : ∀ v, q ≤ C * G.degree v) :
    (highVertices q G).card ≤ 163216 * C := by
  have hEach (v) (hv : v ∈ highVertices q G) :=
    high_vertex_positive_neighbor_sum q G hFree v (Finset.mem_filter.mp hv).2
  have hLower := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul] at hLower
  rw [sum_selected_neighbor_weights] at hLower
  have hUpper : (∑ v, ((G.neighborFinset v ∩ highVertices q G).card : ℤ) *
      positiveDeficiency q G v) ≤ 404 * C * (∑ v, positiveDeficiency q G v) := by
    calc
      _ ≤ ∑ v, (404 * (C : ℤ)) * positiveDeficiency q G v := by
        apply Finset.sum_le_sum
        intro v _
        have hCount : ((G.neighborFinset v ∩ highVertices q G).card : ℤ) ≤ 404 * C := by
          exact_mod_cast high_neighbor_count_le q C hC hq hqC G hFree hDense hMin v
        exact mul_le_mul_of_nonneg_right hCount (positiveDeficiency_nonnegative q G v)
      _ = _ := by rw [← Finset.mul_sum]
  have hPositive := dense_positiveDeficiency_sum_le q hq G hFree hDense
  have hScaled := mul_le_mul_of_nonneg_left hPositive (show 0 ≤ 404 * (C : ℤ) by positivity)
  have hBound : ((highVertices q G).card : ℤ) * (q - 1) ≤ 81608 * C * q := by
    nlinarith [hLower, hUpper, hScaled]
  have hqInt : (8 : ℤ) ≤ q := by exact_mod_cast hq
  have hGap : 0 ≤ ((highVertices q G).card : ℤ) * (q - 2) :=
    mul_nonneg (by positivity) (by omega)
  have hMain : ((highVertices q G).card : ℤ) * q ≤ (163216 * (C : ℤ)) * q := by
    nlinarith [hBound, hGap]
  have hCard := (mul_le_mul_iff_of_pos_right (show (0 : ℤ) < q by omega)).mp hMain
  exact_mod_cast hCard

/-- After the high-vertex bound, the positive deficiency is at most 2q plus a constant. -/
theorem positiveDeficiency_sum_refined (q C : ℕ) (hC : 1 ≤ C) (hq : 8 ≤ q) (hqC : 4 * C ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hMin : ∀ v, q ≤ C * G.degree v) :
    (∑ v, positiveDeficiency q G v) ≤ 2 * (q : ℤ) + 326432 * C := by
  have hSum := positiveDeficiency_sum_le_signed_add_high q G
    (dense_degree_le q (by omega) G hFree hDense)
  have hTotal := dense_total_deficiency_le q G hDense
  have hCount : ((highVertices q G).card : ℤ) ≤ 163216 * C := by
    exact_mod_cast highVertices_card_constant_le q C hC hq hqC G hFree hDense hMin
  omega

/-- A fixed positive minimum-degree ratio excludes degree q+3 for large q. -/
theorem dense_degree_le_add_two (q C : ℕ) (hC : 1 ≤ C) (hq : 8 ≤ q)
    (hqLarge : 327000 * C ^ 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hMin : ∀ v, q ≤ C * G.degree v) (v : Fin (q ^ 2 + q + 2)) :
    G.degree v ≤ q + 2 := by
  classical
  have hqC : 4 * C ≤ q := by nlinarith [sq_nonneg (C - 1 : ℤ)]
  have hDegree := dense_degree_le q (by omega) G hFree hDense v
  by_contra hNot
  have hExact : G.degree v = q + 3 := by omega
  have hNeighbor := neighbor_signedDeficiency_lower q G hFree v
  have hOrder : (q ^ 2 + q + 2 : ℕ) - 1 = q ^ 2 + q + 1 := by omega
  rw [hOrder, hExact] at hNeighbor
  push_cast at hNeighbor
  have hPositive : 2 * (q : ℤ) - 1 ≤
      ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
    have hSigned : 2 * (q : ℤ) - 1 ≤
        ∑ w ∈ G.neighborFinset v, signedDeficiency q G w := by nlinarith
    exact hSigned.trans (Finset.sum_le_sum (fun _ _ => le_max_left _ _))
  have hSubset : (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤
      ∑ w, positiveDeficiency q G w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro w _ _
    exact positiveDeficiency_nonnegative q G w
  have hCard : 1 < (highVertices q G).card := by
    by_contra hSmall
    have hSmall' : ((highVertices q G).card : ℤ) ≤ 1 := by exact_mod_cast (by omega : (highVertices q G).card ≤ 1)
    have hSum := positiveDeficiency_sum_le_signed_add_high q G
      (dense_degree_le q (by omega) G hFree hDense)
    have hTotal := dense_total_deficiency_le q G hDense
    omega
  obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne hCard v
  have hOther := high_vertex_positive_neighbor_sum q G hFree w (Finset.mem_filter.mp hw).2
  let S := G.neighborFinset v
  let T := G.neighborFinset w
  let a := positiveDeficiency q G
  have hIntersectionCard : (S ∩ T).card ≤ 1 := by
    exact codegree_le_one G hFree v w hwv.symm
  have hIntersectionCardInt : ((S ∩ T).card : ℤ) ≤ 1 := by exact_mod_cast hIntersectionCard
  have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
  have hRhs : 0 ≤ (C : ℤ) * ((q : ℤ) + 1) - q := by
    nlinarith [mul_nonneg (show 0 ≤ (C : ℤ) - 1 by omega) (Int.natCast_nonneg q)]
  have hIntersection : (C : ℤ) * (∑ z ∈ S ∩ T, a z) ≤
      C * ((q : ℤ) + 1) - q := by
    calc
      _ = ∑ z ∈ S ∩ T, (C : ℤ) * a z := Finset.mul_sum _ _ _
      _ ≤ ∑ _z ∈ S ∩ T, ((C : ℤ) * ((q : ℤ) + 1) - q) := by
        apply Finset.sum_le_sum
        intro z _
        exact positiveDeficiency_scaled_le q C hC G z (hMin z)
      _ = ((S ∩ T).card : ℤ) * (C * ((q : ℤ) + 1) - q) := by simp; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hIntersectionCardInt hRhs]
  have hUnion : (∑ z ∈ S ∪ T, a z) ≤ ∑ z, a z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro z _ _
    exact positiveDeficiency_nonnegative q G z
  have hIdentity := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := a)
  have hSumLower : 3 * (q : ℤ) - 2 ≤ (∑ z, a z) + (∑ z ∈ S ∩ T, a z) := by
    change (∑ z ∈ S ∪ T, a z) + (∑ z ∈ S ∩ T, a z) =
      (∑ z ∈ S, a z) + (∑ z ∈ T, a z) at hIdentity
    change 2 * (q : ℤ) - 1 ≤ ∑ z ∈ S, a z at hPositive
    change (q : ℤ) - 1 ≤ ∑ z ∈ T, a z at hOther
    linarith
  have hScaled := mul_le_mul_of_nonneg_left hSumLower (Int.natCast_nonneg C)
  have hTotal := positiveDeficiency_sum_refined q C hC hq hqC G hFree hDense hMin
  have hScaledTotal := mul_le_mul_of_nonneg_left hTotal (Int.natCast_nonneg C)
  have hqLargeInt : 327000 * (C : ℤ) ^ 2 ≤ q := by exact_mod_cast hqLarge
  nlinarith [sq_nonneg ((C : ℤ) - 1)]

/-- The zero-codegree matrix with the signed deficiencies on its diagonal. -/
def defectMatrix {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  (zeroCodegreeGraph G).adjMatrix ℤ + Matrix.diagonal (signedDeficiency q G)

theorem defectMatrix_eq {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (SimpleGraph.cycleGraph 4).Free G) :
    defectMatrix q G = Matrix.diagonal (fun _ : Fin n => (q : ℤ)) + allOnesMatrix n -
      G.adjMatrix ℤ * G.adjMatrix ℤ := by
  have h := adjMatrix_square_defect_identity q G hFree
  change _ = _ - defectMatrix q G at h
  rw [h]
  abel

/-- A fourth-walk identity with no asymptotic estimates. -/
theorem defectMatrix_square_identity {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (SimpleGraph.cycleGraph 4).Free G) :
    let A := G.adjMatrix ℤ
    let D := Matrix.diagonal (fun _ : Fin n => (q : ℤ))
    let J := allOnesMatrix n
    let Y := defectMatrix q G
    Y * Y + A * Y * A =
      D * D + D * J + J * D + J * J - D * (A * A) - J * (A * A) -
        (A * A) * D - (A * A) * J + A * D * A + A * J * A := by
  dsimp only
  rw [defectMatrix_eq q G hFree]
  noncomm_ring

theorem adjMatrix_square_row_sum {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (∑ w, (G.adjMatrix ℤ * G.adjMatrix ℤ) v w) =
      ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ) := by
  have h : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ (1 : Fin n → ℤ)) v =
      ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ) := by
    rw [← Matrix.mulVec_mulVec, G.adjMatrix_mulVec_apply]
    simp
  simpa [Matrix.mulVec, dotProduct] using h

theorem adjMatrix_square_column_sum {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (∑ w, (G.adjMatrix ℤ * G.adjMatrix ℤ) w v) =
      ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ) := by
  have hSymm : (G.adjMatrix ℤ * G.adjMatrix ℤ).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul, G.transpose_adjMatrix]
  simp_rw [hSymm.apply v]
  exact adjMatrix_square_row_sum G v

theorem adjMatrix_allOnes_adjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) (v w : Fin n) :
    (G.adjMatrix ℤ * allOnesMatrix n * G.adjMatrix ℤ) v w =
      (G.degree v : ℤ) * G.degree w := by
  have hRow (x : Fin n) : (∑ y, G.adjMatrix ℤ x y) = (G.degree x : ℤ) := by
    have h : (G.adjMatrix ℤ *ᵥ (1 : Fin n → ℤ)) x = (G.degree x : ℤ) := by simp
    simpa [Matrix.mulVec, dotProduct] using h
  have hCol (x : Fin n) : (∑ y, G.adjMatrix ℤ y x) = (G.degree x : ℤ) := by
    simp_rw [G.isSymm_adjMatrix.apply x]
    exact hRow x
  simp only [Matrix.mul_apply, allOnesMatrix, mul_one, hRow, ← Finset.mul_sum, hCol]

/-- At a pair with one common neighbor, the fourth-walk identity simplifies exactly. -/
theorem defectMatrix_pair_identity (q : ℕ) (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hFree : (SimpleGraph.cycleGraph 4).Free G) (v w : Fin (q ^ 2 + q + 2))
    (hvw : v ≠ w) (hCodegree : codegree G v w = 1) :
    (defectMatrix q G * defectMatrix q G) v w +
      (G.adjMatrix ℤ * defectMatrix q G * G.adjMatrix ℤ) v w =
      1 + signedDeficiency q G v * signedDeficiency q G w +
        (∑ x ∈ G.neighborFinset v, signedDeficiency q G x) +
        (∑ x ∈ G.neighborFinset w, signedDeficiency q G x) := by
  have h := congrArg (fun M : Matrix (Fin (q ^ 2 + q + 2))
      (Fin (q ^ 2 + q + 2)) ℤ => M v w) (defectMatrix_square_identity q G hFree)
  have hDiagonal : ((Matrix.diagonal (fun _ : Fin (q ^ 2 + q + 2) => (q : ℤ)) *
      Matrix.diagonal (fun _ : Fin (q ^ 2 + q + 2) => (q : ℤ))) :
      Matrix (Fin (q ^ 2 + q + 2)) (Fin (q ^ 2 + q + 2)) ℤ) v w = 0 := by
    simp [hvw]
  have hMiddle : (G.adjMatrix ℤ *
      Matrix.diagonal (fun _ : Fin (q ^ 2 + q + 2) => (q : ℤ)) * G.adjMatrix ℤ :
      Matrix (Fin (q ^ 2 + q + 2)) (Fin (q ^ 2 + q + 2)) ℤ) v w =
      (q : ℤ) * (G.adjMatrix ℤ * G.adjMatrix ℤ) v w := by
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    simp only [Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hNeighbors (x : Fin (q ^ 2 + q + 2)) :
      (∑ y ∈ G.neighborFinset x, (G.degree y : ℤ)) =
        ((q : ℤ) + 1) * G.degree x - ∑ y ∈ G.neighborFinset x, signedDeficiency q G y := by
    simp [signedDeficiency, Finset.sum_sub_distrib,
      SimpleGraph.card_neighborFinset_eq_degree, mul_comm]
  have hJLeft : (allOnesMatrix (q ^ 2 + q + 2) *
      (G.adjMatrix ℤ * G.adjMatrix ℤ) :
      Matrix (Fin (q ^ 2 + q + 2)) (Fin (q ^ 2 + q + 2)) ℤ) v w =
      ∑ x, (G.adjMatrix ℤ * G.adjMatrix ℤ) x w := by
    simp [Matrix.mul_apply, allOnesMatrix]
  have hJRight : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *
      allOnesMatrix (q ^ 2 + q + 2) :
      Matrix (Fin (q ^ 2 + q + 2)) (Fin (q ^ 2 + q + 2)) ℤ) v w =
      ∑ x, (G.adjMatrix ℤ * G.adjMatrix ℤ) v x := by
    simp [Matrix.mul_apply, allOnesMatrix]
  have hJJ : (allOnesMatrix (q ^ 2 + q + 2) * allOnesMatrix (q ^ 2 + q + 2) :
      Matrix (Fin (q ^ 2 + q + 2)) (Fin (q ^ 2 + q + 2)) ℤ) v w =
      ((q ^ 2 + q + 2 : ℕ) : ℤ) := by
    simp [Matrix.mul_apply, allOnesMatrix]
  simp only [Matrix.add_apply, Matrix.sub_apply] at h
  rw [hDiagonal, hMiddle, hJLeft, hJRight, hJJ,
    adjMatrix_allOnes_adjMatrix, adjMatrix_square_row_sum, adjMatrix_square_column_sum,
    hNeighbors v, hNeighbors w] at h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, allOnesMatrix,
    adjMatrix_square_codegree, hCodegree, Nat.cast_one, mul_one, one_mul] at h
  simp only [signedDeficiency] at h ⊢
  push_cast at h
  nlinarith [h]

/-- A diagonal weight between adjacency matrices sums over common neighbors. -/
theorem adjMatrix_diagonal_adjMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin n → ℤ) (v w : Fin n) :
    (G.adjMatrix ℤ * Matrix.diagonal a * G.adjMatrix ℤ) v w =
      ∑ x ∈ G.neighborFinset v ∩ G.neighborFinset w, a x := by
  rw [Matrix.mul_assoc, G.adjMatrix_mul_apply]
  simp only [Matrix.diagonal_mul]
  have hEntry (x : Fin n) : a x * G.adjMatrix ℤ x w =
      if x ∈ G.neighborFinset w then a x else 0 := by
    by_cases hx : x ∈ G.neighborFinset w
    · have hAdj := (G.mem_neighborFinset w x).mp hx
      simp [hAdj.symm, hx]
    · have hAdj : ¬G.Adj x w := by
        intro h
        exact hx ((G.mem_neighborFinset w x).mpr h.symm)
      simp [hAdj, hx]
  simp_rw [hEntry]
  rw [← Finset.sum_filter]
  congr 1

theorem defectMatrix_square_at_codegree_one {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (v w : Fin n) (hvw : v ≠ w)
    (hCodegree : codegree G v w = 1) :
    (defectMatrix q G * defectMatrix q G) v w =
      ((zeroCodegreeGraph G).adjMatrix ℤ * (zeroCodegreeGraph G).adjMatrix ℤ) v w := by
  have hNot : ¬(zeroCodegreeGraph G).Adj v w := by
    intro h
    change v ≠ w ∧ codegree G v w = 0 at h
    omega
  simp [-SimpleGraph.adjMatrix_mul_apply, -SimpleGraph.mul_adjMatrix_apply,
    defectMatrix, add_mul, mul_add, Matrix.diagonal_mul, Matrix.mul_diagonal, hNot, hvw]

/-- Common zero-codegree partners have a bound in terms of endpoint deficiencies. -/
theorem common_zeroCodegree_partners_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (SimpleGraph.cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2) (v w : Fin (q ^ 2 + q + 2))
    (hvw : v ≠ w) (hCodegree : codegree G v w = 1) :
    (codegree (zeroCodegreeGraph G) v w : ℤ) ≤
      2 + signedDeficiency q G v * signedDeficiency q G w +
        (∑ x ∈ G.neighborFinset v, positiveDeficiency q G x) +
        (∑ x ∈ G.neighborFinset w, positiveDeficiency q G x) := by
  have hIdentity := defectMatrix_pair_identity q G hFree v w hvw hCodegree
  have hExpand : G.adjMatrix ℤ * defectMatrix q G * G.adjMatrix ℤ =
      G.adjMatrix ℤ * (zeroCodegreeGraph G).adjMatrix ℤ * G.adjMatrix ℤ +
      G.adjMatrix ℤ * Matrix.diagonal (signedDeficiency q G) * G.adjMatrix ℤ := by
    unfold defectMatrix
    noncomm_ring
  rw [defectMatrix_square_at_codegree_one q G v w hvw hCodegree,
    hExpand, Matrix.add_apply, adjMatrix_square_codegree,
    adjMatrix_diagonal_adjMatrix] at hIdentity
  have hNonneg : 0 ≤ (G.adjMatrix ℤ * (zeroCodegreeGraph G).adjMatrix ℤ *
      G.adjMatrix ℤ) v w := by
    rw [Matrix.mul_assoc, G.adjMatrix_mul_apply]
    apply Finset.sum_nonneg
    intro x _
    rw [G.mul_adjMatrix_apply]
    apply Finset.sum_nonneg
    intro y _
    simp only [SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have hWeight (x : Fin (q ^ 2 + q + 2)) : (-1 : ℤ) ≤ signedDeficiency q G x := by
    have hCap : (G.degree x : ℤ) ≤ (q : ℤ) + 2 := by exact_mod_cast hDegree x
    unfold signedDeficiency
    omega
  have hSum := Finset.sum_le_sum (fun x (_ : x ∈ G.neighborFinset v ∩ G.neighborFinset w) =>
    hWeight x)
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  have hCard : ((G.neighborFinset v ∩ G.neighborFinset w).card : ℤ) = 1 := by
    exact_mod_cast hCodegree
  rw [hCard] at hSum
  have hPositiveV : (∑ x ∈ G.neighborFinset v, signedDeficiency q G x) ≤
      ∑ x ∈ G.neighborFinset v, positiveDeficiency q G x :=
    Finset.sum_le_sum (fun _ _ => le_max_left _ _)
  have hPositiveW : (∑ x ∈ G.neighborFinset w, signedDeficiency q G x) ≤
      ∑ x ∈ G.neighborFinset w, positiveDeficiency q G x :=
    Finset.sum_le_sum (fun _ _ => le_max_left _ _)
  linarith

/-- Three-edge walks with fixed, ordered endpoints. -/
def threeWalkCount {n : ℕ} (G : SimpleGraph (Fin n)) (v w : Fin n) : ℕ :=
  ∑ x ∈ G.neighborFinset v, codegree G x w

theorem sum_codegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (∑ w, codegree G v w) = ∑ w ∈ G.neighborFinset v, G.degree w := by
  have h : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ (1 : Fin n → ℤ)) v =
      ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ) := by
    rw [← Matrix.mulVec_mulVec, G.adjMatrix_mulVec_apply]
    simp
  have h' : (∑ w, (codegree G v w : ℤ)) =
      ∑ w ∈ G.neighborFinset v, (G.degree w : ℤ) := by
    simpa only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one,
      adjMatrix_square_codegree] using h
  exact_mod_cast h'

theorem threeWalkCount_sum {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (∑ w, threeWalkCount G v w) =
      ∑ x ∈ G.neighborFinset v, ∑ y ∈ G.neighborFinset x, G.degree y := by
  unfold threeWalkCount
  rw [Finset.sum_comm]
  simp_rw [sum_codegree]

theorem threeWalkCount_sum_le {n : ℕ} (G : SimpleGraph (Fin n)) (D : ℕ)
    (hDegree : ∀ v, G.degree v ≤ D) (v : Fin n) :
    (∑ w, threeWalkCount G v w) ≤ G.degree v * D ^ 2 := by
  rw [threeWalkCount_sum]
  calc
    _ ≤ ∑ x ∈ G.neighborFinset v, D ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      calc
        _ ≤ ∑ _y ∈ G.neighborFinset x, D :=
          Finset.sum_le_sum (fun y _ => hDegree y)
        _ = G.degree x * D := by simp
        _ ≤ D ^ 2 := by nlinarith [hDegree x]
    _ = _ := by simp

/-- Many three-edge paths to every nonneighbor force a positive minimum-degree ratio. -/
theorem degree_lower_of_threeWalkCount (q C : ℕ) (hq : 8 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hDegree : ∀ v, G.degree v ≤ q + 3)
    (hPaths : ∀ v w, v ≠ w → ¬G.Adj v w → q ≤ C * threeWalkCount G v w)
    (v : Fin (q ^ 2 + q + 2)) : q ≤ (2 * C) * G.degree v := by
  let S := (Finset.univ.erase v) \ G.neighborFinset v
  have hNeighbors : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro w hw
    have hvw := (G.mem_neighborFinset v w).mp hw
    exact Finset.mem_erase.mpr ⟨hvw.ne.symm, Finset.mem_univ w⟩
  have hCard : S.card + G.degree v + 1 = q ^ 2 + q + 2 := by
    have h : S.card + G.degree v = q ^ 2 + q + 1 := by
      simpa [S, SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_sdiff_add_card_eq_card hNeighbors
    omega
  have hEach (w) (hw : w ∈ S) : q ≤ C * threeWalkCount G v w := by
    have hMem := Finset.mem_sdiff.mp hw
    have hNe := (Finset.mem_erase.mp hMem.1).1.symm
    exact hPaths v w hNe (fun h => hMem.2 ((G.mem_neighborFinset v w).mpr h))
  have hLower := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hLower
  have hSubset : (∑ w ∈ S, threeWalkCount G v w) ≤ ∑ w, threeWalkCount G v w :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hUpper := threeWalkCount_sum_le G (q + 3) hDegree v
  have hBound := hLower.trans (Nat.mul_le_mul_left C (hSubset.trans hUpper))
  have hBoundInt : (S.card : ℤ) * q ≤ C * (G.degree v * (q + 3) ^ 2 : ℕ) := by
    exact_mod_cast hBound
  have hDegreeInt : (G.degree v : ℤ) ≤ (q : ℤ) + 3 := by exact_mod_cast hDegree v
  have hCardInt : (S.card : ℤ) + G.degree v + 1 = (q : ℤ) ^ 2 + q + 2 := by
    exact_mod_cast hCard
  have hqInt : (8 : ℤ) ≤ q := by exact_mod_cast hq
  have hPositive : (0 : ℤ) < S.card := by nlinarith [sq_nonneg ((q : ℤ) - 1)]
  have hCompare : ((q : ℤ) + 3) ^ 2 ≤ 2 * S.card := by
    nlinarith [sq_nonneg ((q : ℤ) - 8)]
  have hScaled := mul_le_mul_of_nonneg_left hCompare
    (show 0 ≤ (C : ℤ) * G.degree v by positivity)
  push_cast at hBoundInt
  have hMain : (S.card : ℤ) * q ≤ S.card * (2 * C * G.degree v) := by
    nlinarith [hBoundInt, hScaled]
  have hResult := (mul_le_mul_iff_of_pos_left hPositive).mp hMain
  exact_mod_cast hResult

/-- Add one specified nonloop edge to a graph. -/
def withEdge {n : ℕ} (G : SimpleGraph (Fin n)) (v w : Fin n) (hvw : v ≠ w) :
    SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∨ (x = v ∧ y = w) ∨ (x = w ∧ y = v)
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h
    · exact h.ne rfl
    · exact hvw (h.1.symm.trans h.2)
    · exact hvw (h.2.symm.trans h.1)⟩

theorem withEdge_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w) :
    (withEdge G v w hvw).edgeFinset = insert s(v, w) G.edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert]
    change (G.Adj x y ∨ (x = v ∧ y = w) ∨ (x = w ∧ y = v)) ↔ _
    simp only [Sym2.eq_iff]
    tauto

theorem withEdge_edge_count {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w) (hNonedge : ¬G.Adj v w) :
    (withEdge G v w hvw).edgeFinset.card = G.edgeFinset.card + 1 := by
  rw [withEdge_edgeFinset, Finset.card_insert_of_notMem]
  simpa using hNonedge

/-- Every cycle created by a single edge addition traverses that edge. -/
theorem withEdge_copy_hits_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v w : Fin n) (hvw : v ≠ w)
    (f : (cycleGraph 4).Copy (withEdge G v w hvw)) :
    ∃ i : Fin 4, (f i = v ∧ f (i + 1) = w) ∨ (f i = w ∧ f (i + 1) = v) := by
  by_contra hNone
  apply hFree
  refine ⟨{ toHom := { toFun := f, map_rel' := ?_ }, injective' := f.injective }⟩
  intro i j hij
  have hAdj := f.toHom.map_rel' hij
  change G.Adj (f i) (f j) ∨ (f i = v ∧ f j = w) ∨ (f i = w ∧ f j = v) at hAdj
  rcases hAdj with h | h | h
  · exact h
  all_goals
    have hStep : j = i + 1 ∨ i = j + 1 := by
      have h : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → j = i + 1 ∨ i = j + 1 := by decide
      exact h i j hij
    exfalso
  · rcases hStep with hStep | hStep
    · exact hNone ⟨i, Or.inl ⟨h.1, by simpa only [hStep] using h.2⟩⟩
    · exact hNone ⟨j, Or.inr ⟨h.2, by simpa only [hStep] using h.1⟩⟩
  · rcases hStep with hStep | hStep
    · exact hNone ⟨i, Or.inr ⟨h.1, by simpa only [hStep] using h.2⟩⟩
    · exact hNone ⟨j, Or.inl ⟨h.2, by simpa only [hStep] using h.1⟩⟩

/-- At an internal cycle vertex, each incident edge belongs to the original graph. -/
theorem withEdge_adj_of_internal {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w) (x y : Fin n) (hxv : x ≠ v) (hxw : x ≠ w)
    (h : (withEdge G v w hvw).Adj x y) : G.Adj x y := by
  rcases h with h | h | h
  · exact h
  · exact False.elim (hxv h.1)
  · exact False.elim (hxw h.1)

/-- A cycle starting with the new oriented edge determines a three-edge old path. -/
theorem withEdge_copy_forward_form {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w)
    (f : (cycleGraph 4).Copy (withEdge G v w hvw)) (h0 : f 0 = v) (h1 : f 1 = w) :
    G.Adj v (f 3) ∧ G.Adj (f 3) (f 2) ∧ G.Adj w (f 2) := by
  have hInternal (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : f i ≠ v ∧ f i ≠ w := by
    constructor
    · intro h
      exact hi0 (f.injective (h.trans h0.symm))
    · intro h
      exact hi1 (f.injective (h.trans h1.symm))
  have h2 := hInternal 2 (by decide) (by decide)
  have h3 := hInternal 3 (by decide) (by decide)
  have h30 := withEdge_adj_of_internal G v w hvw (f 3) (f 0) h3.1 h3.2
    (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 3 0))
  have h32 := withEdge_adj_of_internal G v w hvw (f 3) (f 2) h3.1 h3.2
    (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 3 2))
  have h21 := withEdge_adj_of_internal G v w hvw (f 2) (f 1) h2.1 h2.2
    (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 2 1))
  exact ⟨by simpa only [h0] using h30.symm, h32, by simpa only [h1] using h21.symm⟩

theorem withEdge_copy_reverse_form {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w)
    (f : (cycleGraph 4).Copy (withEdge G v w hvw)) (h0 : f 0 = w) (h1 : f 1 = v) :
    G.Adj v (f 2) ∧ G.Adj (f 2) (f 3) ∧ G.Adj w (f 3) := by
  have hInternal (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : f i ≠ v ∧ f i ≠ w := by
    constructor
    · intro h
      exact hi1 (f.injective (h.trans h1.symm))
    · intro h
      exact hi0 (f.injective (h.trans h0.symm))
  have h2 := hInternal 2 (by decide) (by decide)
  have h3 := hInternal 3 (by decide) (by decide)
  have h21 := withEdge_adj_of_internal G v w hvw (f 2) (f 1) h2.1 h2.2
    (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 2 1))
  have h23 := withEdge_adj_of_internal G v w hvw (f 2) (f 3) h2.1 h2.2
    (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 2 3))
  have h30 := withEdge_adj_of_internal G v w hvw (f 3) (f 0) h3.1 h3.2
    (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 3 0))
  exact ⟨by simpa only [h1] using h21.symm, h23, by simpa only [h0] using h30.symm⟩

/-- A new labelled cycle is determined by an old three-edge path and its orientation. -/
theorem withEdge_copy_parameters {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v w : Fin n) (hvw : v ≠ w)
    (f : (cycleGraph 4).Copy (withEdge G v w hvw)) :
    ∃ (i : Fin 4) (b : Bool) (a c : Fin n),
      G.Adj v a ∧ G.Adj a c ∧ G.Adj w c ∧
        (fun j => f j) = fun j =>
          (if b then ![w, v, a, c] else ![v, w, c, a]) (j - i) := by
  obtain ⟨i, hi⟩ := withEdge_copy_hits_edge G hFree v w hvw f
  let g := rotateFourCopy f i
  rcases hi with hi | hi
  · have h0 : g 0 = v := by
      change f (i + 0) = v
      simpa using hi.1
    have h1 : g 1 = w := hi.2
    obtain ⟨ha, hac, hc⟩ := withEdge_copy_forward_form G v w hvw g h0 h1
    refine ⟨i, false, g 3, g 2, ha, hac, hc, ?_⟩
    have hForm : (fun j => g j) = ![v, w, g 2, g 3] := by
      funext j
      fin_cases j <;> simp [h0, h1]
    funext j
    have hValue := congrFun hForm (j - i)
    change f (i + (j - i)) = _ at hValue
    rw [add_comm i, sub_add_cancel] at hValue
    exact hValue
  · have h0 : g 0 = w := by
      change f (i + 0) = w
      simpa using hi.1
    have h1 : g 1 = v := hi.2
    obtain ⟨ha, hac, hc⟩ := withEdge_copy_reverse_form G v w hvw g h0 h1
    refine ⟨i, true, g 2, g 3, ha, hac, hc, ?_⟩
    have hForm : (fun j => g j) = ![w, v, g 2, g 3] := by
      funext j
      fin_cases j <;> simp [h0, h1]
    funext j
    have hValue := congrFun hForm (j - i)
    change f (i + (j - i)) = _ at hValue
    rw [add_comm i, sub_add_cancel] at hValue
    exact hValue

/-- A uniform bound for the actual subgraph count after adding one edge. -/
theorem withEdge_copyCount_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v w : Fin n) (hvw : v ≠ w) :
    (withEdge G v w hvw).copyCount (cycleGraph 4) ≤ 8 * threeWalkCount G v w := by
  let H := withEdge G v w hvw
  let paths : Finset (Σ _ : Fin n, Fin n) :=
    (G.neighborFinset v).sigma fun a => G.neighborFinset a ∩ G.neighborFinset w
  let parameters : Finset (Fin 4 × Bool × (Σ _ : Fin n, Fin n)) :=
    Finset.univ.product (Finset.univ.product paths)
  let forms : Finset (Fin 4 → Fin n) := parameters.image fun p j =>
    (if p.2.1 then ![w, v, p.2.2.1, p.2.2.2] else ![v, w, p.2.2.2, p.2.2.1]) (j - p.1)
  have hf (f : (cycleGraph 4).Copy H) : (fun j => f j) ∈ forms := by
    obtain ⟨i, b, a, c, ha, hac, hc, hForm⟩ := withEdge_copy_parameters G hFree v w hvw f
    apply Finset.mem_image.mpr
    refine ⟨(i, b, ⟨a, c⟩), ?_, hForm.symm⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact Finset.mem_sigma.mpr ⟨(G.mem_neighborFinset v a).mpr ha,
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a c).mpr hac, (G.mem_neighborFinset w c).mpr hc⟩⟩
  have hCopies : (Finset.univ : Finset ((cycleGraph 4).Copy H)).card ≤ forms.card := by
    apply Finset.card_le_card_of_injOn (fun f : (cycleGraph 4).Copy H => fun j => f j)
    · exact fun f _ => hf f
    · intro f _ g _ hfg
      apply SimpleGraph.Copy.ext
      exact congrFun hfg
  calc
    H.copyCount (cycleGraph 4) =
        ((Finset.univ : Finset ((cycleGraph 4).Copy H)).image SimpleGraph.Copy.toSubgraph).card :=
      SimpleGraph.copyCount_eq_card_image_copyToSubgraph
    _ ≤ (Finset.univ : Finset ((cycleGraph 4).Copy H)).card := Finset.card_image_le
    _ ≤ forms.card := hCopies
    _ ≤ parameters.card := Finset.card_image_le
    _ = 8 * threeWalkCount G v w := by
      simp [parameters, paths, Finset.card_sigma, threeWalkCount, codegree]
      ring

/-- The absence of a cheap added edge gives the required minimum-degree ratio. -/
theorem degree_lower_of_no_cheap_edge (q C : ℕ) (hq : 8 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hNoCheap : ∀ v w (hvw : v ≠ w), ¬G.Adj v w →
      q ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4))
    (v : Fin (q ^ 2 + q + 2)) : q ≤ (16 * C) * G.degree v := by
  have hPaths (x y) (hxy : x ≠ y) (hNonedge : ¬G.Adj x y) :
      q ≤ (8 * C) * threeWalkCount G x y := by
    have hLower := hNoCheap x y hxy hNonedge
    have hUpper := Nat.mul_le_mul_left C (withEdge_copyCount_le G hFree x y hxy)
    nlinarith
  have h := degree_lower_of_threeWalkCount q (8 * C) hq G
    (dense_degree_le q (by omega) G hFree hDense) hPaths v
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- The no-cheap-edge assumption supplies all preliminary degree and mass bounds. -/
theorem degree_preparation_of_no_cheap_edge (q C : ℕ) (hC : 1 ≤ C) (hq : 8 ≤ q)
    (hqLarge : 327000 * (16 * C) ^ 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hNoCheap : ∀ v w (hvw : v ≠ w), ¬G.Adj v w →
      q ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4)) :
    (∀ v, q ≤ (16 * C) * G.degree v) ∧
      (∀ v, G.degree v ≤ q + 2) ∧
      (highVertices q G).card ≤ 2611456 * C ∧
      (∑ v, positiveDeficiency q G v) ≤ 2 * (q : ℤ) + 5222912 * C := by
  have hMin := degree_lower_of_no_cheap_edge q C hq G hFree hDense hNoCheap
  have hRatio : 1 ≤ 16 * C := by omega
  have hRange : 4 * (16 * C) ≤ q := by nlinarith
  refine ⟨hMin, dense_degree_le_add_two q (16 * C) hRatio hq hqLarge G hFree hDense hMin, ?_, ?_⟩
  · have h := highVertices_card_constant_le q (16 * C) hRatio hq hRange G hFree hDense hMin
    nlinarith
  · have h := positiveDeficiency_sum_refined q (16 * C) hRatio hq hRange G hFree hDense hMin
    push_cast at h
    nlinarith

/-- Vertices at positive entries of a residual row. -/
def positivePartners {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w => 0 < weightedResidual q G v w

def positiveResidualMass {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : ℤ :=
  ∑ w, max (weightedResidual q G v w) 0

def negativeResidualMass {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : ℤ :=
  ∑ w, max (-weightedResidual q G v w) 0

theorem weightedResidual_symmetric {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    (weightedResidual q G).IsSymm := by
  have hJ : (allOnesMatrix n).IsSymm := rfl
  have hSquare : (weightedAdjacency q G * weightedAdjacency q G).IsSymm := by
    change (weightedAdjacency q G * weightedAdjacency q G)ᵀ = _
    rw [Matrix.transpose_mul, weightedAdjacency_symmetric q G]
  exact ((Matrix.isSymm_diagonal _).add hJ).sub hSquare

theorem positiveResidualMass_balance (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (v : Fin (q ^ 2 + q + 2)) :
    positiveResidualMass q G v = 1 + negativeResidualMass q G v := by
  have hEntry (w) : max (weightedResidual q G v w) 0 =
      weightedResidual q G v w + max (-weightedResidual q G v w) 0 := by omega
  have hRow := congrFun (above_plane_residual_row_sum q G) v
  have hRow' : (∑ w, weightedResidual q G v w) = 1 := by
    simpa [Matrix.mulVec, dotProduct] using hRow
  unfold positiveResidualMass negativeResidualMass
  simp_rw [hEntry]
  rw [Finset.sum_add_distrib, hRow']

theorem positivePartners_card_le_mass {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    ((positivePartners q G v).card : ℤ) ≤ positiveResidualMass q G v := by
  have hCount : ((positivePartners q G v).card : ℤ) =
      ∑ w, if 0 < weightedResidual q G v w then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter]
    simp [positivePartners]
  rw [hCount]
  apply Finset.sum_le_sum
  intro w _
  split_ifs <;> omega

theorem signedDeficiency_ge_neg_one {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ w, G.degree w ≤ q + 2) (v : Fin n) :
    (-1 : ℤ) ≤ signedDeficiency q G v := by
  have h : (G.degree v : ℤ) ≤ (q : ℤ) + 2 := by exact_mod_cast hDegree v
  unfold signedDeficiency
  omega

/-- Every positive entry in a low residual row has weight one. -/
theorem low_residual_entry_le_one {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ w, G.degree w ≤ q + 2) (v : Fin n)
    (hLow : 1 ≤ signedDeficiency q G v) (w : Fin n) :
    weightedResidual q G v w ≤ 1 := by
  by_cases hvw : v = w
  · subst w
    rw [weightedResidual_diagonal]
    have hProduct := int_mul_pred_nonnegative (signedDeficiency q G v)
    nlinarith
  · rw [weightedResidual_off_diagonal q G v w hvw, adjMatrix_square_codegree]
    have hWeight := signedDeficiency_ge_neg_one q G hDegree w
    have hCodegree : (0 : ℤ) ≤ codegree G v w := by positivity
    by_cases hAdj : G.Adj v w
    · simp only [G.adjMatrix_apply, ite_eq_left hAdj, one_mul]
      omega
    · simp only [G.adjMatrix_apply, ite_eq_right hAdj, zero_mul, sub_zero]
      omega

theorem low_positivePartners_card_eq_mass {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ w, G.degree w ≤ q + 2) (v : Fin n)
    (hLow : 1 ≤ signedDeficiency q G v) :
    ((positivePartners q G v).card : ℤ) = positiveResidualMass q G v := by
  have hCount : ((positivePartners q G v).card : ℤ) =
      ∑ w, if 0 < weightedResidual q G v w then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter]
    simp [positivePartners]
  rw [hCount]
  apply Finset.sum_congr rfl
  intro w _
  have hUpper := low_residual_entry_le_one q G hDegree v hLow w
  split_ifs <;> omega

/-- A nonhigh positive partner of a low is a nonneighbor with zero codegree. -/
theorem positivePartner_nonhigh {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v w : Fin n) (hLow : 1 ≤ signedDeficiency q G v)
    (hNonhigh : 0 ≤ signedDeficiency q G w) (hPartner : w ∈ positivePartners q G v) :
    v ≠ w ∧ ¬G.Adj v w ∧ codegree G v w = 0 := by
  have hPositive := (Finset.mem_filter.mp hPartner).2
  have hNe : v ≠ w := by
    intro h
    subst w
    rw [weightedResidual_diagonal] at hPositive
    have hProduct := int_mul_pred_nonnegative (signedDeficiency q G v)
    nlinarith
  rw [weightedResidual_off_diagonal q G v w hNe, adjMatrix_square_codegree] at hPositive
  have hCodegree : (0 : ℤ) ≤ codegree G v w := by positivity
  have hNot : ¬G.Adj v w := by
    intro hAdj
    simp only [G.adjMatrix_apply, ite_eq_left hAdj, one_mul] at hPositive
    omega
  simp only [G.adjMatrix_apply, ite_eq_right hNot, zero_mul, sub_zero] at hPositive
  refine ⟨hNe, hNot, ?_⟩
  have hZero : (codegree G v w : ℤ) = 0 := by omega
  exact_mod_cast hZero

theorem nonlow_negativeResidual_entry_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) (hNonhigh : signedDeficiency q G v ≤ 0)
    (w : Fin n) (hvw : v ≠ w) :
    max (-weightedResidual q G v w) 0 ≤
      if G.Adj v w then positiveDeficiency q G w else 0 := by
  rw [weightedResidual_off_diagonal q G v w hvw, adjMatrix_square_codegree]
  have hCard : (codegree G v w : ℤ) ≤ 1 := by exact_mod_cast codegree_le_one G hFree v w hvw
  have hNonnegative : (0 : ℤ) ≤ codegree G v w := by positivity
  by_cases hAdj : G.Adj v w
  · simp only [G.adjMatrix_apply, ite_eq_left hAdj, one_mul, positiveDeficiency]
    omega
  · simp only [G.adjMatrix_apply, ite_eq_right hAdj, zero_mul, sub_zero]
    omega

/-- The mass of a nonhigh row is controlled by its neighboring positive deficiencies. -/
theorem nonlow_positiveResidualMass_le_diagonal (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hNonhigh : signedDeficiency q G v ≤ 0) :
    positiveResidualMass q G v ≤ 1 + signedDeficiency q G v ^ 2 - signedDeficiency q G v +
      ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  have hPointwise (w : Fin (q ^ 2 + q + 2)) : max (-weightedResidual q G v w) 0 ≤
      (if w = v then signedDeficiency q G v ^ 2 - signedDeficiency q G v else 0) +
      (if G.Adj v w then positiveDeficiency q G w else 0) := by
    by_cases hw : w = v
    · subst w
      rw [weightedResidual_diagonal]
      have hProduct := int_mul_pred_nonnegative (signedDeficiency q G v)
      have hNot : ¬G.Adj v v := fun h => G.ne_of_adj h rfl
      simp only [ite_eq_right hNot, add_zero]
      have hDiff : 0 ≤ signedDeficiency q G v ^ 2 - signedDeficiency q G v := by nlinarith
      change max (-(signedDeficiency q G v - signedDeficiency q G v ^ 2)) 0 ≤
        signedDeficiency q G v ^ 2 - signedDeficiency q G v
      apply max_le
      · linarith
      · exact hDiff
    · simp only [ite_eq_right hw, zero_add]
      exact nonlow_negativeResidual_entry_le q G hFree v hNonhigh w (Ne.symm hw)
  have hSum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hPointwise w)
  simp only [Finset.sum_add_distrib] at hSum
  have hNeighbors : (∑ w, if G.Adj v w then positiveDeficiency q G w else 0) =
      ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
    rw [G.neighborFinset_eq_filter, Finset.sum_filter]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left, hNeighbors] at hSum
  rw [positiveResidualMass_balance]
  change negativeResidualMass q G v ≤ _ at hSum
  linarith

theorem regular_positivePartners_card_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hRegular : signedDeficiency q G v = 0) :
    ((positivePartners q G v).card : ℤ) ≤
      1 + ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  have h := nonlow_positiveResidualMass_le_diagonal q G hFree v (by omega)
  rw [hRegular] at h
  exact (positivePartners_card_le_mass q G v).trans (by simpa using h)

theorem codegree_symm {n : ℕ} (G : SimpleGraph (Fin n)) (v w : Fin n) :
    codegree G v w = codegree G w v := by
  simp only [codegree, Finset.inter_comm]

theorem codegree_eq_zero_iff {n : ℕ} (G : SimpleGraph (Fin n)) (v w : Fin n) :
    codegree G v w = 0 ↔ ∀ x, G.Adj v x → ¬G.Adj w x := by
  constructor
  · intro h x hvx hwx
    have hEmpty : G.neighborFinset v ∩ G.neighborFinset w = ∅ := Finset.card_eq_zero.mp h
    have hx : x ∈ G.neighborFinset v ∩ G.neighborFinset w :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v x).mpr hvx, (G.mem_neighborFinset w x).mpr hwx⟩
    simp [hEmpty] at hx
  · intro h
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxv, hxw⟩ := Finset.mem_inter.mp hx
    exact h x ((G.mem_neighborFinset v x).mp hxv) ((G.mem_neighborFinset w x).mp hxw)

theorem weightedAdjacency_mul_apply {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (M : Matrix (Fin n) (Fin n) ℤ) (v w : Fin n) :
    (weightedAdjacency q G * M) v w =
      (∑ x ∈ G.neighborFinset v, M x w) + signedDeficiency q G v * M v w := by
  simp only [weightedAdjacency, add_mul, Matrix.add_apply, G.adjMatrix_mul_apply,
    Matrix.diagonal_mul]

theorem mul_weightedAdjacency_apply {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (M : Matrix (Fin n) (Fin n) ℤ) (v w : Fin n) :
    (M * weightedAdjacency q G) v w =
      (∑ x ∈ G.neighborFinset w, M v x) + M v w * signedDeficiency q G w := by
  simp only [weightedAdjacency, mul_add, Matrix.add_apply, G.mul_adjMatrix_apply,
    Matrix.mul_diagonal]

theorem weightedResidual_nonadj {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w) (hNot : ¬G.Adj v w) :
    weightedResidual q G v w = 1 - (codegree G v w : ℤ) := by
  rw [weightedResidual_off_diagonal q G v w hvw, adjMatrix_square_codegree]
  simp only [G.adjMatrix_apply, ite_eq_right hNot, zero_mul, sub_zero]

theorem weightedResidual_nonadj_nonnegative {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v w : Fin n) (hvw : v ≠ w) (hNot : ¬G.Adj v w) :
    0 ≤ weightedResidual q G v w := by
  rw [weightedResidual_nonadj q G v w hvw hNot]
  have hCount : (codegree G v w : ℤ) ≤ 1 := by exact_mod_cast codegree_le_one G hFree v w hvw
  omega

theorem weightedResidual_regular_neighbor {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v w : Fin n) (hAdj : G.Adj v w) (hRegular : signedDeficiency q G v = 0) :
    weightedResidual q G v w = 1 - (codegree G v w : ℤ) - signedDeficiency q G w := by
  rw [weightedResidual_off_diagonal q G v w hAdj.ne, adjMatrix_square_codegree]
  simp only [G.adjMatrix_apply, ite_eq_left hAdj, hRegular, zero_add, one_mul]

/-- A triangular regular neighbor covers every untriangulated regular neighbor through its positive row. -/
theorem regular_triangle_positive_cover {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l x v : Fin n)
    (hLX : G.Adj l x) (hLV : G.Adj l v)
    (hX : signedDeficiency q G x = 0) (hV : signedDeficiency q G v = 0)
    (hTri : codegree G l x = 1) (hUntri : codegree G l v = 0) :
    ∃ w ∈ G.neighborFinset v, w ∈ positivePartners q G x := by
  have hXV : x ≠ v := by intro h; subst v; omega
  have hNotXV : ¬G.Adj x v := by
    intro h
    exact (codegree_eq_zero_iff G l v).mp hUntri x hLX h.symm
  have hZLV : weightedResidual q G l v = 1 - signedDeficiency q G l := by
    rw [weightedResidual_off_diagonal q G l v hLV.ne, adjMatrix_square_codegree]
    simp only [G.adjMatrix_apply, ite_eq_left hLV, hUntri, Nat.cast_zero, hV, add_zero, one_mul,
      sub_zero]
  have hZXL : weightedResidual q G x l = -signedDeficiency q G l := by
    rw [weightedResidual_regular_neighbor q G x l hLX.symm hX, codegree_symm G x l, hTri]
    simp
  have hLNX : l ∈ G.neighborFinset x := (G.mem_neighborFinset x l).mpr hLX.symm
  have hLNV : l ∈ G.neighborFinset v := (G.mem_neighborFinset v l).mpr hLV.symm
  have hLeftRest : 0 ≤ ∑ z ∈ (G.neighborFinset x).erase l, weightedResidual q G z v := by
    apply Finset.sum_nonneg
    intro z hz
    have hZL := (Finset.mem_erase.mp hz).1
    have hXZ := (G.mem_neighborFinset x z).mp (Finset.mem_erase.mp hz).2
    have hZV : z ≠ v := by intro h; subst z; exact hNotXV hXZ
    have hNotZV : ¬G.Adj z v := by
      intro h
      have hEq := common_neighbor_unique G hFree hXV hLX.symm hLV.symm hXZ h.symm
      exact hZL hEq.symm
    exact weightedResidual_nonadj_nonnegative q G hFree z v hZV hNotZV
  have hLeft := Finset.sum_erase_add (G.neighborFinset x)
    (fun z => weightedResidual q G z v) hLNX
  rw [hZLV] at hLeft
  have hLeftBound : 1 - signedDeficiency q G l ≤
      ∑ z ∈ G.neighborFinset x, weightedResidual q G z v := by linarith
  by_contra hNone
  push Not at hNone
  have hRightRest : (∑ z ∈ (G.neighborFinset v).erase l, weightedResidual q G x z) ≤ 0 := by
    apply Finset.sum_nonpos
    intro z hz
    have hNot := hNone z (Finset.mem_erase.mp hz).2
    have hNonpos : ¬0 < weightedResidual q G x z := by
      intro h
      exact hNot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have hRight := Finset.sum_erase_add (G.neighborFinset v)
    (fun z => weightedResidual q G x z) hLNV
  rw [hZXL] at hRight
  have hRightBound : (∑ z ∈ G.neighborFinset v, weightedResidual q G x z) ≤
      -signedDeficiency q G l := by linarith
  have hComm := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M x v)
    (weightedAdjacency_commutes_residual q G)
  simp only [weightedAdjacency_mul_apply, mul_weightedAdjacency_apply,
    hX, hV, zero_mul, mul_zero, add_zero] at hComm
  linarith

/-- Summing positive deficiency twice along edges uses each off-diagonal endpoint at most once. -/
theorem selected_neighbor_positive_weight_sum_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) (S : Finset (Fin n))
    (hSubset : S ⊆ G.neighborFinset v) :
    (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, positiveDeficiency q G y) ≤
      (S.card : ℤ) * positiveDeficiency q G v + ∑ y, positiveDeficiency q G y := by
  have hRest := nonreturning_neighbor_weight_sum_le G hFree v S hSubset
    (positiveDeficiency q G) (positiveDeficiency_nonnegative q G)
  have hEntry (x) (hx : x ∈ S) :
      (∑ y ∈ G.neighborFinset x, positiveDeficiency q G y) =
      positiveDeficiency q G v + ∑ y ∈ (G.neighborFinset x).erase v, positiveDeficiency q G y := by
    have hVX : v ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x v).mpr ((G.mem_neighborFinset v x).mp (hSubset hx)).symm
    have h := Finset.sum_erase_add (G.neighborFinset x) (positiveDeficiency q G) hVX
    linarith
  calc
    _ = ∑ x ∈ S,
        (positiveDeficiency q G v + ∑ y ∈ (G.neighborFinset x).erase v, positiveDeficiency q G y) :=
      Finset.sum_congr rfl hEntry
    _ = (S.card : ℤ) * positiveDeficiency q G v +
        ∑ x ∈ S, ∑ y ∈ (G.neighborFinset x).erase v, positiveDeficiency q G y := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by linarith

theorem neighbor_positive_weight_sum_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) :
    (∑ x ∈ G.neighborFinset v, ∑ y ∈ G.neighborFinset x, positiveDeficiency q G y) ≤
      (G.degree v : ℤ) * positiveDeficiency q G v + ∑ y, positiveDeficiency q G y := by
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    selected_neighbor_positive_weight_sum_le q G hFree v (G.neighborFinset v) (fun _ h => h)

/-- Regular neighbors of a vertex. -/
def regularNeighbors {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v).filter fun w => signedDeficiency q G w = 0

/-- Regular neighbors whose incident edge lies in a triangle. -/
def triangularRegularNeighbors {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) : Finset (Fin n) :=
  (regularNeighbors q G v).filter fun w => codegree G v w = 1

theorem untriangulated_regular_neighbor {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v w : Fin n)
    (hw : w ∈ regularNeighbors q G v \ triangularRegularNeighbors q G v) :
    G.Adj v w ∧ signedDeficiency q G w = 0 ∧ codegree G v w = 0 := by
  obtain ⟨hRegular, hNotTri⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨hNeighbor, hZero⟩ := Finset.mem_filter.mp hRegular
  have hAdj := (G.mem_neighborFinset v w).mp hNeighbor
  have hCodegree := codegree_le_one G hFree v w hAdj.ne
  have hNotOne : codegree G v w ≠ 1 := by
    intro h
    exact hNotTri (Finset.mem_filter.mpr ⟨hRegular, h⟩)
  exact ⟨hAdj, hZero, by omega⟩

/-- Positive partners give an injection from untriangulated regular neighbors. -/
theorem triangular_regular_neighbor_cover_bound (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (x : Fin (q ^ 2 + q + 2)) (hx : x ∈ triangularRegularNeighbors q G l) :
    ((regularNeighbors q G l).card : ℤ) - (triangularRegularNeighbors q G l).card - 1 ≤
      ∑ w ∈ G.neighborFinset x, positiveDeficiency q G w := by
  let R := regularNeighbors q G l
  let T := triangularRegularNeighbors q G l
  let U := R \ T
  obtain ⟨hxRegular, hxTri⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxNeighbor, hxZero⟩ := Finset.mem_filter.mp hxRegular
  have hLX := (G.mem_neighborFinset l x).mp hxNeighbor
  have hZXL : weightedResidual q G x l = -signedDeficiency q G l := by
    rw [weightedResidual_regular_neighbor q G x l hLX.symm hxZero, codegree_symm G x l, hxTri]
    simp
  have hNotL : l ∉ positivePartners q G x := by
    intro h
    have hPositive := (Finset.mem_filter.mp h).2
    rw [hZXL] at hPositive
    omega
  have hCover (v) (hv : v ∈ U) : ∃ w, w ∈ positivePartners q G x ∧ G.Adj w v := by
    obtain ⟨hLV, hvZero, hvUntri⟩ := untriangulated_regular_neighbor q G hFree l v hv
    obtain ⟨w, hwNeighbor, hwPositive⟩ :=
      regular_triangle_positive_cover q G hFree l x v hLX hLV hxZero hvZero hxTri hvUntri
    exact ⟨w, hwPositive, ((G.mem_neighborFinset v w).mp hwNeighbor).symm⟩
  let cover : Fin (q ^ 2 + q + 2) → Fin (q ^ 2 + q + 2) :=
    fun v => if hv : v ∈ U then (hCover v hv).choose else x
  have hSpec (v) (hv : v ∈ U) : cover v ∈ positivePartners q G x ∧ G.Adj (cover v) v := by
    dsimp only [cover]
    rw [dite_eq_left hv]
    exact (hCover v hv).choose_spec
  have hCount : U.card ≤ (positivePartners q G x).card := by
    apply Finset.card_le_card_of_injOn cover
    · intro v hv
      exact (hSpec v hv).1
    · intro v hv w hw hEqual
      have hLV := (untriangulated_regular_neighbor q G hFree l v hv).1
      have hLW := (untriangulated_regular_neighbor q G hFree l w hw).1
      have hCV := (hSpec v hv).2
      have hCW := (hSpec w hw).2
      rw [← hEqual] at hCW
      have hDistinct : l ≠ cover v := by
        intro h
        exact hNotL (h ▸ (hSpec v hv).1)
      exact common_neighbor_unique G hFree hDistinct hLV hCV hLW hCW
  have hSubset : T ⊆ R := Finset.filter_subset _ _
  have hPartition : U.card + T.card = R.card := Finset.card_sdiff_add_card_eq_card hSubset
  have hCountInt : (U.card : ℤ) ≤ (positivePartners q G x).card := by exact_mod_cast hCount
  have hPartitionInt : (U.card : ℤ) + T.card = R.card := by exact_mod_cast hPartition
  have hMass := regular_positivePartners_card_le q G hFree x hxZero
  change (R.card : ℤ) - T.card - 1 ≤ _
  omega

/-- The triangle cover controls the regular triangular edges around a low vertex. -/
theorem triangle_cover_bound (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l) :
    ((triangularRegularNeighbors q G l).card : ℤ) *
        (((regularNeighbors q G l).card : ℤ) - (triangularRegularNeighbors q G l).card - 1) ≤
      signedDeficiency q G l * G.degree l + ∑ v, positiveDeficiency q G v := by
  have hEach (x) (hx : x ∈ triangularRegularNeighbors q G l) :=
    triangular_regular_neighbor_cover_bound q G hFree l hLow x hx
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  have hSubset : triangularRegularNeighbors q G l ⊆ G.neighborFinset l := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hBound :
      (∑ x ∈ triangularRegularNeighbors q G l, ∑ y ∈ G.neighborFinset x, positiveDeficiency q G y) ≤
      ∑ x ∈ G.neighborFinset l, ∑ y ∈ G.neighborFinset x, positiveDeficiency q G y := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
    intro x _ _
    exact Finset.sum_nonneg (fun y _ => positiveDeficiency_nonnegative q G y)
  have hFinal := neighbor_positive_weight_sum_le q G hFree l
  have hPositive : positiveDeficiency q G l = signedDeficiency q G l := by
    exact max_eq_left (by omega)
  rw [hPositive] at hFinal
  nlinarith [hSum, hBound, hFinal]

theorem weightedResidual_negative_diagonal {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) :
    max (-weightedResidual q G v v) 0 = signedDeficiency q G v ^ 2 - signedDeficiency q G v := by
  rw [weightedResidual_diagonal]
  have hProduct := int_mul_pred_nonnegative (signedDeficiency q G v)
  have hNonnegative : 0 ≤ signedDeficiency q G v ^ 2 - signedDeficiency q G v := by nlinarith
  have hValue : -(signedDeficiency q G v - signedDeficiency q G v ^ 2) =
      signedDeficiency q G v ^ 2 - signedDeficiency q G v := by ring
  rw [hValue, max_eq_left hNonnegative]

/-- Negative residual mass comes from the diagonal and the incident graph edges. -/
theorem negativeResidualMass_formula {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) :
    negativeResidualMass q G v = signedDeficiency q G v ^ 2 - signedDeficiency q G v +
      ∑ w ∈ G.neighborFinset v,
        max (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0 := by
  have hPointwise (w : Fin n) : max (-weightedResidual q G v w) 0 =
      (if w = v then signedDeficiency q G v ^ 2 - signedDeficiency q G v else 0) +
      (if G.Adj v w then
        max (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0 else 0) := by
    by_cases hw : w = v
    · subst w
      have hNot : ¬G.Adj v v := fun h => G.ne_of_adj h rfl
      rw [ite_eq_left rfl, ite_eq_right hNot, add_zero]
      exact weightedResidual_negative_diagonal q G v
    · rw [ite_eq_right hw, zero_add]
      by_cases hAdj : G.Adj v w
      · rw [ite_eq_left hAdj, weightedResidual_off_diagonal q G v w (Ne.symm hw),
          adjMatrix_square_codegree]
        simp only [G.adjMatrix_apply, ite_eq_left hAdj, one_mul]
        congr 1
        ring
      · rw [ite_eq_right hAdj]
        have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree v w (Ne.symm hw) hAdj
        exact max_eq_right (by omega)
  have hDiagonal : (∑ w : Fin n, if w = v then
      signedDeficiency q G v ^ 2 - signedDeficiency q G v else 0) =
      signedDeficiency q G v ^ 2 - signedDeficiency q G v := by simp
  have hNeighbor : (∑ w, if G.Adj v w then
      max (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0 else 0) =
      ∑ w ∈ G.neighborFinset v,
        max (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0 := by
    rw [G.neighborFinset_eq_filter, Finset.sum_filter]
  unfold negativeResidualMass
  simp_rw [hPointwise]
  rw [Finset.sum_add_distrib, hDiagonal, hNeighbor]

/-- Exact positive-row cardinality for a nonunit low vertex. -/
theorem nonunit_positivePartners_card (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (v : Fin (q ^ 2 + q + 2))
    (hLow : 2 ≤ signedDeficiency q G v) :
    ((positivePartners q G v).card : ℤ) =
      (signedDeficiency q G v - 1) * q + signedDeficiency q G v +
      (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) +
      ∑ w ∈ G.neighborFinset v, (codegree G v w : ℤ) := by
  have hRaw := negativeResidualMass_formula q G hFree v
  have hEntry (w : Fin (q ^ 2 + q + 2)) :
      max (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0 =
      signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1 := by
    have hWeight := signedDeficiency_ge_neg_one q G hDegree w
    have hCodegree : (0 : ℤ) ≤ codegree G v w := by positivity
    exact max_eq_left (by omega)
  simp_rw [hEntry] at hRaw
  rw [low_positivePartners_card_eq_mass q G hDegree v (by omega), positiveResidualMass_balance, hRaw]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    SimpleGraph.card_neighborFinset_eq_degree]
  have hDegreeEq : (G.degree v : ℤ) = (q : ℤ) + 1 - signedDeficiency q G v := by
    unfold signedDeficiency
    ring
  rw [hDegreeEq]
  ring

/-- All low rows satisfy the positive-deficiency version of the row-size bound. -/
theorem low_positiveResidualMass_upper (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G v) :
    positiveResidualMass q G v ≤
      (signedDeficiency q G v - 1) * q + signedDeficiency q G v +
      (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) +
      ∑ w ∈ G.neighborFinset v, (codegree G v w : ℤ) := by
  have hRaw := negativeResidualMass_formula q G hFree v
  have hEntry (w : Fin (q ^ 2 + q + 2)) :
      max (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0 ≤
      signedDeficiency q G v - 1 + positiveDeficiency q G w + (codegree G v w : ℤ) := by
    have hWeight : signedDeficiency q G w ≤ positiveDeficiency q G w := le_max_left _ _
    have hPositive := positiveDeficiency_nonnegative q G w
    have hCodegree : (0 : ℤ) ≤ codegree G v w := by positivity
    apply max_le <;> omega
  have hSum := Finset.sum_le_sum (fun w (_ : w ∈ G.neighborFinset v) => hEntry w)
  calc
    positiveResidualMass q G v = 1 + (signedDeficiency q G v ^ 2 - signedDeficiency q G v +
        ∑ w ∈ G.neighborFinset v,
          max (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0) := by
      rw [positiveResidualMass_balance, hRaw]
    _ ≤ 1 + (signedDeficiency q G v ^ 2 - signedDeficiency q G v +
        ∑ w ∈ G.neighborFinset v,
          (signedDeficiency q G v - 1 + positiveDeficiency q G w + (codegree G v w : ℤ))) := by
      linarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        SimpleGraph.card_neighborFinset_eq_degree]
      have hDegreeEq : (G.degree v : ℤ) = (q : ℤ) + 1 - signedDeficiency q G v := by
        unfold signedDeficiency
        ring
      rw [hDegreeEq]
      ring

theorem low_positivePartners_card_upper (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G v) :
    ((positivePartners q G v).card : ℤ) ≤
      (signedDeficiency q G v - 1) * q + signedDeficiency q G v +
      (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) +
      ∑ w ∈ G.neighborFinset v, (codegree G v w : ℤ) :=
  (positivePartners_card_le_mass q G v).trans (low_positiveResidualMass_upper q G hFree v hLow)

/-- The signed-deficiency expression is a lower bound even for unit low rows. -/
theorem low_positivePartners_card_lower (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (v : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G v) :
    (signedDeficiency q G v - 1) * q + signedDeficiency q G v +
      (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) +
      (∑ w ∈ G.neighborFinset v, (codegree G v w : ℤ)) ≤
      ((positivePartners q G v).card : ℤ) := by
  have hRaw := negativeResidualMass_formula q G hFree v
  have hSum := Finset.sum_le_sum (fun w (_ : w ∈ G.neighborFinset v) =>
    le_max_left (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1) 0)
  calc
    _ = 1 + (signedDeficiency q G v ^ 2 - signedDeficiency q G v +
        ∑ w ∈ G.neighborFinset v,
          (signedDeficiency q G v + signedDeficiency q G w + (codegree G v w : ℤ) - 1)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        SimpleGraph.card_neighborFinset_eq_degree]
      have hDegreeEq : (G.degree v : ℤ) = (q : ℤ) + 1 - signedDeficiency q G v := by
        unfold signedDeficiency
        ring
      rw [hDegreeEq]
      ring
    _ ≤ 1 + negativeResidualMass q G v := by rw [hRaw]; linarith
    _ = _ := by rw [← positiveResidualMass_balance, low_positivePartners_card_eq_mass q G hDegree v hLow]

theorem weightedAdjacency_off_diagonal {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w) : weightedAdjacency q G v w = G.adjMatrix ℤ v w := by
  simp [weightedAdjacency, hvw]

theorem weightedAdjacency_adj {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v w : Fin n) (hAdj : G.Adj v w) : weightedAdjacency q G v w = 1 := by
  rw [weightedAdjacency_off_diagonal q G v w hAdj.ne]
  simp only [G.adjMatrix_apply, ite_eq_left hAdj]

theorem weightedAdjacency_nonadj {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v w : Fin n) (hvw : v ≠ w) (hNot : ¬G.Adj v w) : weightedAdjacency q G v w = 0 := by
  rw [weightedAdjacency_off_diagonal q G v w hvw]
  simp only [G.adjMatrix_apply, ite_eq_right hNot]

theorem weightedAdjacency_nonhigh_column_nonnegative {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (v : Fin n) (hNonhigh : 0 ≤ signedDeficiency q G v)
    (w : Fin n) : 0 ≤ weightedAdjacency q G w v := by
  by_cases hw : w = v
  · subst w
    have hDiagonal : weightedAdjacency q G v v = signedDeficiency q G v := by
      simp [weightedAdjacency]
    rwa [hDiagonal]
  · rw [weightedAdjacency_off_diagonal q G w v hw]
    simp only [G.adjMatrix_apply]
    split <;> norm_num

/-- Commutation converts a positive-row block count to a signed residual sum. -/
theorem positive_block_commutator_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l v : Fin n) (hNonhigh : 0 ≤ signedDeficiency q G v) :
    ((G.neighborFinset v ∩ positivePartners q G l).card : ℤ) ≤
      (weightedAdjacency q G * weightedResidual q G) l v +
        ∑ w, max (-weightedResidual q G l w) 0 * weightedAdjacency q G w v := by
  let S := G.neighborFinset v ∩ positivePartners q G l
  have hWeights (w) (hw : w ∈ S) :
      (1 : ℤ) ≤ max (weightedResidual q G l w) 0 * weightedAdjacency q G w v := by
    obtain ⟨hNeighbor, hPartner⟩ := Finset.mem_inter.mp hw
    have hAdj := ((G.mem_neighborFinset v w).mp hNeighbor).symm
    rw [weightedAdjacency_adj q G w v hAdj, mul_one]
    have hPositive := (Finset.mem_filter.mp hPartner).2
    omega
  have hNonnegative (w) : 0 ≤ max (weightedResidual q G l w) 0 * weightedAdjacency q G w v :=
    mul_nonneg (le_max_right _ _) (weightedAdjacency_nonhigh_column_nonnegative q G v hNonhigh w)
  have hDecompose (w) :
      max (weightedResidual q G l w) 0 * weightedAdjacency q G w v =
      weightedResidual q G l w * weightedAdjacency q G w v +
        max (-weightedResidual q G l w) 0 * weightedAdjacency q G w v := by
    have h : max (weightedResidual q G l w) 0 =
        weightedResidual q G l w + max (-weightedResidual q G l w) 0 := by omega
    rw [h]
    ring
  calc
    (S.card : ℤ) = ∑ _w ∈ S, (1 : ℤ) := by simp
    _ ≤ ∑ w ∈ S, max (weightedResidual q G l w) 0 * weightedAdjacency q G w v :=
      Finset.sum_le_sum hWeights
    _ ≤ ∑ w, max (weightedResidual q G l w) 0 * weightedAdjacency q G w v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro w _ _
      exact hNonnegative w
    _ = (weightedResidual q G * weightedAdjacency q G) l v +
        ∑ w, max (-weightedResidual q G l w) 0 * weightedAdjacency q G w v := by
      simp_rw [hDecompose]
      rw [Finset.sum_add_distrib, Matrix.mul_apply]
    _ = _ := by rw [← weightedAdjacency_commutes_residual]

theorem sum_if_neighbor_eq_inter {n : ℕ} (G : SimpleGraph (Fin n))
    (l v : Fin n) (a : Fin n → ℤ) :
    (∑ w ∈ G.neighborFinset l, if G.Adj v w then a w else 0) =
      ∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v, a w := by
  rw [← Finset.sum_filter]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]

/-- At a nonedge, the negative-row correction is supported on the common neighbors. -/
theorem negative_row_correction_nonedge {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hlv : l ≠ v) (hNot : ¬G.Adj l v) :
    (∑ w, max (-weightedResidual q G l w) 0 * weightedAdjacency q G w v) =
      ∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v,
        max (signedDeficiency q G l + signedDeficiency q G w + (codegree G l w : ℤ) - 1) 0 := by
  have hPoint (w : Fin n) :
      max (-weightedResidual q G l w) 0 * weightedAdjacency q G w v =
        if G.Adj l w ∧ G.Adj v w then
          max (signedDeficiency q G l + signedDeficiency q G w + (codegree G l w : ℤ) - 1) 0 else 0 := by
    by_cases hw : w = v
    · subst w
      have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree l v hlv hNot
      have hZero : max (-weightedResidual q G l v) 0 = 0 := max_eq_right (by omega)
      simp only [hZero, zero_mul, hNot, false_and, ite_false]
    · by_cases hVW : G.Adj v w
      · rw [weightedAdjacency_adj q G w v hVW.symm, mul_one]
        by_cases hLW : G.Adj l w
        · rw [ite_eq_left ⟨hLW, hVW⟩, weightedResidual_off_diagonal q G l w hLW.ne,
            adjMatrix_square_codegree]
          simp only [G.adjMatrix_apply, ite_eq_left hLW, one_mul]
          congr 1
          ring
        · have hLWNe : l ≠ w := by intro h; subst w; exact hNot hVW.symm
          have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree l w hLWNe hLW
          have hZero : max (-weightedResidual q G l w) 0 = 0 := max_eq_right (by omega)
          simp only [hZero, hLW, false_and, ite_false]
      · have hWV : ¬G.Adj w v := fun h => hVW h.symm
        rw [weightedAdjacency_nonadj q G w v hw hWV, mul_zero]
        simp only [hVW, and_false, ite_false]
  simp_rw [hPoint]
  rw [← Finset.sum_filter]
  congr 1
  ext w
  simp [G.neighborFinset_eq_filter]

/-- The common-neighbor deficiency cancels against its negative-row correction. -/
theorem residual_common_neighbor_cancellation {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l v w : Fin n) (hLow : 1 ≤ signedDeficiency q G l)
    (hNonhigh : 0 ≤ signedDeficiency q G v) (hWV : G.Adj w v) :
    weightedResidual q G w v +
        max (signedDeficiency q G l + signedDeficiency q G w + (codegree G l w : ℤ) - 1) 0 ≤
      max (weightedResidual q G w v) 0 + (signedDeficiency q G l - 1) +
        (codegree G l w : ℤ) + (if 0 < signedDeficiency q G w then 1 else 0) := by
  have hCodegree : (0 : ℤ) ≤ codegree G l w := by positivity
  have hOtherCodegree : (0 : ℤ) ≤ codegree G w v := by positivity
  have hEntry : weightedResidual q G w v =
      1 - (codegree G w v : ℤ) - (signedDeficiency q G w + signedDeficiency q G v) := by
    rw [weightedResidual_off_diagonal q G w v hWV.ne, adjMatrix_square_codegree]
    simp only [G.adjMatrix_apply, ite_eq_left hWV, one_mul]
  by_cases hPositive : 0 < signedDeficiency q G w
  · have hCorner : 0 ≤ signedDeficiency q G l + signedDeficiency q G w +
        (codegree G l w : ℤ) - 1 := by omega
    rw [ite_eq_left hPositive, max_eq_left hCorner]
    have hMax : 0 ≤ max (weightedResidual q G w v) 0 := le_max_right _ _
    linarith
  · have hCorner : max (signedDeficiency q G l + signedDeficiency q G w +
        (codegree G l w : ℤ) - 1) 0 ≤ signedDeficiency q G l - 1 + codegree G l w := by
      apply max_le <;> omega
    rw [ite_eq_right hPositive]
    have hMax := le_max_left (weightedResidual q G w v) 0
    linarith

/-- Pointwise block bound, including the low common-neighbor cancellation. -/
theorem positive_row_block_bound {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hlv : l ≠ v) (hNot : ¬G.Adj l v)
    (hLow : 1 ≤ signedDeficiency q G l) (hNonhigh : 0 ≤ signedDeficiency q G v) :
    ((G.neighborFinset v ∩ positivePartners q G l).card : ℤ) ≤
      signedDeficiency q G l - (codegree G l v : ℤ) +
        (∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v,
          ((codegree G l w : ℤ) + (if 0 < signedDeficiency q G w then 1 else 0))) +
        ∑ w ∈ G.neighborFinset l, max (weightedResidual q G w v) 0 := by
  have hVia := positive_block_commutator_le q G l v hNonhigh
  rw [negative_row_correction_nonedge q G hFree l v hlv hNot,
    weightedAdjacency_mul_apply, weightedResidual_nonadj q G l v hlv hNot] at hVia
  have hEach (w) (hw : w ∈ G.neighborFinset l) :
      weightedResidual q G w v +
          (if G.Adj v w then max (signedDeficiency q G l + signedDeficiency q G w +
            (codegree G l w : ℤ) - 1) 0 else 0) ≤
        max (weightedResidual q G w v) 0 +
          (if G.Adj v w then (signedDeficiency q G l - 1) +
            ((codegree G l w : ℤ) + (if 0 < signedDeficiency q G w then 1 else 0)) else 0) := by
    by_cases hAdj : G.Adj v w
    · simp only [ite_eq_left hAdj]
      have h := residual_common_neighbor_cancellation q G l v w hLow hNonhigh hAdj.symm
      linarith
    · simp only [ite_eq_right hAdj, add_zero]
      exact le_max_left _ _
  have hSum := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hSum
  simp only [sum_if_neighbor_eq_inter] at hSum
  have hExtra : (∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v,
      ((signedDeficiency q G l - 1) +
        ((codegree G l w : ℤ) + (if 0 < signedDeficiency q G w then 1 else 0)))) =
      (signedDeficiency q G l - 1) * (codegree G l v : ℤ) +
        ∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v,
          ((codegree G l w : ℤ) + (if 0 < signedDeficiency q G w then 1 else 0)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, codegree]
    ring
  rw [hExtra] at hSum
  nlinarith [hVia, hSum]

theorem triangle_edge_count_le_degree {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) :
    (∑ w ∈ G.neighborFinset v, (codegree G v w : ℤ)) ≤ G.degree v := by
  have hEach (w) (hw : w ∈ G.neighborFinset v) : (codegree G v w : ℤ) ≤ 1 := by
    exact_mod_cast codegree_le_one G hFree v w ((G.mem_neighborFinset v w).mp hw).ne
  have hSum := Finset.sum_le_sum hEach
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree] using hSum

/-- The positive mass of a low row has a linear bound in its deficiency. -/
theorem low_positiveResidualMass_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G v) :
    positiveResidualMass q G v ≤ (q : ℤ) * signedDeficiency q G v + 1 +
      ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  have hUpper := low_positiveResidualMass_upper q G hFree v hLow
  have hTriangles := triangle_edge_count_le_degree G hFree v
  have hDegree : (G.degree v : ℤ) + signedDeficiency q G v = q + 1 := by
    unfold signedDeficiency
    omega
  nlinarith

theorem nonlow_positiveResidualMass_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (v : Fin (q ^ 2 + q + 2))
    (hNonlow : signedDeficiency q G v ≤ 0) :
    positiveResidualMass q G v ≤ 3 + ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  have hLower := signedDeficiency_ge_neg_one q G hDegree v
  have hCases : signedDeficiency q G v = 0 ∨ signedDeficiency q G v = -1 := by omega
  have hUpper := nonlow_positiveResidualMass_le_diagonal q G hFree v hNonlow
  rcases hCases with h | h <;> rw [h] at hUpper <;> norm_num at hUpper <;> linarith

/-- First moment of the positive residual contributions from low neighbors. -/
theorem low_neighbor_positive_mass_sum_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l) :
    let S := (G.neighborFinset l).filter fun w => 0 < signedDeficiency q G w
    (∑ w ∈ S, positiveResidualMass q G w) ≤
      (q : ℤ) * (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) +
        (signedDeficiency q G l + 1) * S.card + ∑ y, positiveDeficiency q G y := by
  dsimp only
  let S := (G.neighborFinset l).filter fun w => 0 < signedDeficiency q G w
  have hEach (w) (hw : w ∈ S) := low_positiveResidualMass_le q G hFree w
    (by have h := (Finset.mem_filter.mp hw).2; omega)
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one] at hSum
  have hWeights : (∑ w ∈ S, signedDeficiency q G w) =
      ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    unfold positiveDeficiency
    split_ifs <;> omega
  rw [hWeights] at hSum
  have hSelected := selected_neighbor_positive_weight_sum_le q G hFree l S (Finset.filter_subset _ _)
  have hPositive : positiveDeficiency q G l = signedDeficiency q G l := max_eq_left (by omega)
  rw [hPositive] at hSelected
  change (∑ w ∈ S, positiveResidualMass q G w) ≤ _
  nlinarith

/-- First moment of the positive residual contributions from nonlow neighbors. -/
theorem nonlow_neighbor_positive_mass_sum_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) :
    let S := (G.neighborFinset l).filter fun w => signedDeficiency q G w ≤ 0
    (∑ w ∈ S, positiveResidualMass q G w) ≤
      signedDeficiency q G l * G.degree l + 3 * G.degree l + ∑ y, positiveDeficiency q G y := by
  dsimp only
  let S := (G.neighborFinset l).filter fun w => signedDeficiency q G w ≤ 0
  have hEach (w) (hw : w ∈ S) := nonlow_positiveResidualMass_le q G hFree hDegree w
    (Finset.mem_filter.mp hw).2
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hSum
  have hSelected := selected_neighbor_positive_weight_sum_le q G hFree l S (Finset.filter_subset _ _)
  have hPositive : positiveDeficiency q G l = signedDeficiency q G l := max_eq_left (by omega)
  rw [hPositive] at hSelected
  have hCard : (S.card : ℤ) ≤ G.degree l := by
    exact_mod_cast (show S.card ≤ G.degree l by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (Finset.filter_subset (fun w => signedDeficiency q G w ≤ 0) (G.neighborFinset l)))
  have hScaled := mul_le_mul_of_nonneg_left hCard
    (show 0 ≤ signedDeficiency q G l + 3 by omega)
  change (∑ w ∈ S, positiveResidualMass q G w) ≤ _
  nlinarith

/-- Blocks on nonhigh positive partners vanish at the low vertex and its neighbors. -/
theorem nonhigh_positive_block_empty {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l : Fin n) (hLow : 1 ≤ signedDeficiency q G l) (S : Finset (Fin n))
    (hSubset : S ⊆ positivePartners q G l)
    (hNonhigh : ∀ w ∈ S, 0 ≤ signedDeficiency q G w)
    (v : Fin n) (hCenter : v = l ∨ G.Adj l v) :
    G.neighborFinset v ∩ S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwNeighbor, hwS⟩ := Finset.mem_inter.mp hw
  have hvw := (G.mem_neighborFinset v w).mp hwNeighbor
  obtain ⟨_, hNot, hCodegree⟩ := positivePartner_nonhigh q G l w hLow
    (hNonhigh w hwS) (hSubset hwS)
  rcases hCenter with hCenter | hCenter
  · subst v
    exact hNot hvw
  · exact (codegree_eq_zero_iff G l w).mp hCodegree v hCenter hvw.symm

/-- Count the incidences between two vertex sets in either order. -/
theorem sum_neighbor_intersection_card {n : ℕ} (G : SimpleGraph (Fin n))
    (C P : Finset (Fin n)) :
    (∑ v ∈ C, (G.neighborFinset v ∩ P).card) =
      ∑ w ∈ P, (G.neighborFinset w ∩ C).card := by
  have hCount (v : Fin n) (S : Finset (Fin n)) :
      (G.neighborFinset v ∩ S).card = ∑ w ∈ S, if G.Adj v w then 1 else 0 := by
    rw [← Finset.sum_filter]
    have hFilter : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by
      ext w
      simp [G.neighborFinset_eq_filter, and_comm]
    rw [hFilter]
    simp
  calc
    _ = ∑ v ∈ C, ∑ w ∈ P, if G.Adj v w then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact hCount v P
    _ = ∑ w ∈ P, ∑ v ∈ C, if G.Adj v w then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      simpa only [SimpleGraph.adj_comm] using (hCount w C).symm

/-- Large neighbor blocks in a four-cycle-free graph satisfy the incidence packing bound. -/
theorem large_neighbor_blocks_incidence_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P C : Finset (Fin n)) (t : ℝ) (ht : 0 ≤ t)
    (hLarge : ∀ v ∈ C, t ≤ ((G.neighborFinset v ∩ P).card : ℝ)) :
    (t ^ 2 - P.card) * (∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℝ)) ≤
      P.card * t ^ 2 := by
  let I : ℝ := ∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℝ)
  let m : ℝ := P.card
  let r : ℝ := C.card
  have hI : 0 ≤ I := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hTotal : I = ∑ w ∈ P, ((G.neighborFinset w ∩ C).card : ℝ) := by
    dsimp [I]
    exact_mod_cast sum_neighbor_intersection_card G C P
  have hPairs : (∑ w ∈ P, ((G.neighborFinset w ∩ C).card.choose 2 : ℝ)) ≤
      (C.card.choose 2 : ℝ) := by
    exact_mod_cast sum_choose_neighbors_in_set_le G hFree P C
  have hPairScaled : 2 * (∑ w ∈ P, ((G.neighborFinset w ∩ C).card.choose 2 : ℝ)) ≤ r ^ 2 - r := by
    calc
      _ ≤ 2 * (C.card.choose 2 : ℝ) := mul_le_mul_of_nonneg_left hPairs (by norm_num)
      _ = _ := by rw [Nat.cast_choose_two]; dsimp [r]; ring
  have hTerm (w : Fin n) : ((G.neighborFinset w ∩ C).card : ℝ) ^ 2 =
      2 * ((G.neighborFinset w ∩ C).card.choose 2 : ℝ) + (G.neighborFinset w ∩ C).card := by
    rw [Nat.cast_choose_two]
    ring
  have hSquares : (∑ w ∈ P, ((G.neighborFinset w ∩ C).card : ℝ) ^ 2) ≤ I + r ^ 2 := by
    simp_rw [hTerm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hTotal]
    linarith
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun _ => (1 : ℝ)) (fun w => ((G.neighborFinset w ∩ C).card : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCauchy
  rw [← hTotal] at hCauchy
  have hSquareBound : I ^ 2 ≤ m * (I + r ^ 2) :=
    hCauchy.trans (mul_le_mul_of_nonneg_left hSquares hm)
  have hThreshold : r * t ≤ I := by
    calc
      _ = ∑ _v ∈ C, t := by simp [r]
      _ ≤ _ := Finset.sum_le_sum hLarge
  have hThresholdSquared : r ^ 2 * t ^ 2 ≤ I ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg hr ht) hI).mpr hThreshold
  have hScaled := mul_le_mul_of_nonneg_right hSquareBound (sq_nonneg t)
  have hThresholdScaled := mul_le_mul_of_nonneg_left hThresholdSquared hm
  have hPolynomial : (t ^ 2 - m) * I ^ 2 ≤ m * t ^ 2 * I := by
    nlinarith [hScaled, hThresholdScaled]
  change (t ^ 2 - m) * I ≤ m * t ^ 2
  by_cases hZero : I = 0
  · rw [hZero, mul_zero]
    exact mul_nonneg hm (sq_nonneg t)
  · have hPositive : 0 < I := lt_of_le_of_ne hI (Ne.symm hZero)
    apply (mul_le_mul_iff_of_pos_right hPositive).mp
    nlinarith [hPolynomial]

theorem large_neighbor_blocks_incidence_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P C : Finset (Fin n)) (t : ℝ) (ht : 0 ≤ t)
    (hLarge : ∀ v ∈ C, t ≤ ((G.neighborFinset v ∩ P).card : ℝ))
    (hGap : (P.card : ℝ) < t ^ 2) :
    (∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℝ)) ≤ P.card * t ^ 2 / (t ^ 2 - P.card) := by
  apply (le_div_iff₀ (sub_pos.mpr hGap)).mpr
  simpa only [mul_comm] using large_neighbor_blocks_incidence_bound G hFree P C t ht hLarge

/-- The second factorial moment of a sum of zero-one entries counts distinct ordered pairs. -/
theorem binary_sum_factorial_moment {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → ℤ) (hb : ∀ i ∈ S, b i * b i = b i) :
    (∑ i ∈ S, b i) ^ 2 - (∑ i ∈ S, b i) =
      ∑ i ∈ S, ∑ j ∈ S.erase i, b i * b j := by
  have hTerm (i) (hi : i ∈ S) :
      b i * (∑ j ∈ S, b j) - b i = ∑ j ∈ S.erase i, b i * b j := by
    have hErase := Finset.sum_erase_add S (fun j => b i * b j) hi
    rw [hb i hi] at hErase
    rw [Finset.mul_sum]
    linarith
  rw [pow_two, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl hTerm

/-- Count ordered pairs of incident rows by their common columns. -/
theorem incidence_factorial_moment {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ) (N : ι → Finset κ) :
    (∑ v ∈ T, (((S.filter fun w => v ∈ N w).card : ℤ) ^ 2 -
      (S.filter fun w => v ∈ N w).card)) =
      ∑ w ∈ S, ∑ u ∈ S.erase w, ((T ∩ N w ∩ N u).card : ℤ) := by
  let b : ι → κ → ℤ := fun w v => if v ∈ N w then 1 else 0
  have hCount (v) : ((S.filter fun w => v ∈ N w).card : ℤ) = ∑ w ∈ S, b w v := by
    dsimp only [b]
    rw [← Finset.sum_filter]
    simp
  have hIdempotent (v w) : b w v * b w v = b w v := by
    dsimp only [b]
    split_ifs <;> norm_num
  have hRow (v) : ((S.filter fun w => v ∈ N w).card : ℤ) ^ 2 -
      (S.filter fun w => v ∈ N w).card = ∑ w ∈ S, ∑ u ∈ S.erase w, b w v * b u v := by
    rw [hCount]
    exact binary_sum_factorial_moment S (fun w => b w v) (fun w _ => hIdempotent v w)
  have hOverlap (w u) : (∑ v ∈ T, b w v * b u v) = ((T ∩ N w ∩ N u).card : ℤ) := by
    have hProduct (v) : b w v * b u v = if v ∈ N w ∧ v ∈ N u then 1 else 0 := by
      dsimp only [b]
      split_ifs <;> simp_all
    simp_rw [hProduct]
    rw [← Finset.sum_filter]
    have hFilter : (T.filter fun v => v ∈ N w ∧ v ∈ N u) = T ∩ N w ∩ N u := by
      ext v
      simp
    rw [hFilter]
    simp
  calc
    _ = ∑ v ∈ T, ∑ w ∈ S, ∑ u ∈ S.erase w, b w v * b u v := Finset.sum_congr rfl (fun v _ => hRow v)
    _ = ∑ w ∈ S, ∑ v ∈ T, ∑ u ∈ S.erase w, b w v * b u v := Finset.sum_comm
    _ = ∑ w ∈ S, ∑ u ∈ S.erase w, ∑ v ∈ T, b w v * b u v := by
      apply Finset.sum_congr rfl
      intro w _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro u _
      exact hOverlap w u

/-- Common nonhigh positive partners of two lows are zero-codegree partners of both. -/
theorem nonhigh_positivePartners_overlap_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (T : Finset (Fin (q ^ 2 + q + 2)))
    (hT : ∀ v ∈ T, 0 ≤ signedDeficiency q G v)
    (w u : Fin (q ^ 2 + q + 2)) (hW : 1 ≤ signedDeficiency q G w)
    (hU : 1 ≤ signedDeficiency q G u) (hWU : w ≠ u) (hCodegree : codegree G w u = 1) :
    ((T ∩ positivePartners q G w ∩ positivePartners q G u).card : ℤ) ≤
      2 + signedDeficiency q G w * signedDeficiency q G u +
        (∑ v ∈ G.neighborFinset w, positiveDeficiency q G v) +
        (∑ v ∈ G.neighborFinset u, positiveDeficiency q G v) := by
  have hSubset : T ∩ positivePartners q G w ∩ positivePartners q G u ⊆
      (zeroCodegreeGraph G).neighborFinset w ∩ (zeroCodegreeGraph G).neighborFinset u := by
    intro v hv
    obtain ⟨hvTW, hvU⟩ := Finset.mem_inter.mp hv
    obtain ⟨hvT, hvW⟩ := Finset.mem_inter.mp hvTW
    obtain ⟨hWV, _, hWZero⟩ := positivePartner_nonhigh q G w v hW (hT v hvT) hvW
    obtain ⟨hUV, _, hUZero⟩ := positivePartner_nonhigh q G u v hU (hT v hvT) hvU
    apply Finset.mem_inter.mpr
    constructor
    · apply ((zeroCodegreeGraph G).mem_neighborFinset w v).mpr
      exact ⟨hWV, hWZero⟩
    · apply ((zeroCodegreeGraph G).mem_neighborFinset u v).mpr
      exact ⟨hUV, hUZero⟩
  have hCard : ((T ∩ positivePartners q G w ∩ positivePartners q G u).card : ℤ) ≤
      codegree (zeroCodegreeGraph G) w u := by
    exact_mod_cast Finset.card_le_card hSubset
  exact hCard.trans (common_zeroCodegree_partners_le q G hFree hDegree w u hWU hCodegree)

/-- The low-neighbor second moment is bounded by their deficiency and incidence sums. -/
theorem low_neighbor_incidence_second_moment (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (S T : Finset (Fin (q ^ 2 + q + 2))) (hS : S ⊆ G.neighborFinset l)
    (hLowS : ∀ w ∈ S, 1 ≤ signedDeficiency q G w)
    (hT : ∀ v ∈ T, 0 ≤ signedDeficiency q G v) :
    (∑ v ∈ T, (((S.filter fun w => v ∈ positivePartners q G w).card : ℤ) ^ 2 -
      (S.filter fun w => v ∈ positivePartners q G w).card)) ≤
      2 * (S.card : ℤ) ^ 2 + (∑ w ∈ S, signedDeficiency q G w) ^ 2 +
        2 * S.card * ((S.card : ℤ) * signedDeficiency q G l + ∑ y, positiveDeficiency q G y) := by
  let c : Fin (q ^ 2 + q + 2) → ℤ :=
    fun w => ∑ v ∈ G.neighborFinset w, positiveDeficiency q G v
  have hc (w) : 0 ≤ c w := Finset.sum_nonneg (fun v _ => positiveDeficiency_nonnegative q G v)
  have hPair (w) (hw : w ∈ S) (u) (hu : u ∈ S.erase w) :
      ((T ∩ positivePartners q G w ∩ positivePartners q G u).card : ℤ) ≤
        2 + signedDeficiency q G w * signedDeficiency q G u + c w + c u := by
    have huS := (Finset.mem_erase.mp hu).2
    have hWU : w ≠ u := (Finset.mem_erase.mp hu).1.symm
    have hWL := ((G.mem_neighborFinset l w).mp (hS hw)).symm
    have hUL := ((G.mem_neighborFinset l u).mp (hS huS)).symm
    have hPositive : 0 < codegree G w u := by
      apply Finset.card_pos.mpr
      exact ⟨l, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w l).mpr hWL,
        (G.mem_neighborFinset u l).mpr hUL⟩⟩
    have hCodegree : codegree G w u = 1 := by
      have hUpper := codegree_le_one G hFree w u hWU
      omega
    exact nonhigh_positivePartners_overlap_le q G hFree hDegree T hT w u
      (hLowS w hw) (hLowS u huS) hWU hCodegree
  have hPairs : (∑ w ∈ S, ∑ u ∈ S.erase w,
      ((T ∩ positivePartners q G w ∩ positivePartners q G u).card : ℤ)) ≤
      ∑ w ∈ S, ∑ u ∈ S, (2 + signedDeficiency q G w * signedDeficiency q G u + c w + c u) := by
    apply Finset.sum_le_sum
    intro w hw
    calc
      _ ≤ ∑ u ∈ S.erase w, (2 + signedDeficiency q G w * signedDeficiency q G u + c w + c u) :=
        Finset.sum_le_sum (fun u hu => hPair w hw u hu)
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro u hu _
        have hW := hLowS w hw
        have hU := hLowS u hu
        have hProduct : 0 ≤ signedDeficiency q G w * signedDeficiency q G u :=
          mul_nonneg (by omega) (by omega)
        linarith [hc w, hc u]
  have hAllPairs : (∑ w ∈ S, ∑ u ∈ S,
      (2 + signedDeficiency q G w * signedDeficiency q G u + c w + c u)) =
      2 * (S.card : ℤ) ^ 2 + (∑ w ∈ S, signedDeficiency q G w) ^ 2 +
        2 * S.card * (∑ w ∈ S, c w) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [incidence_factorial_moment]
  have hFirst := selected_neighbor_positive_weight_sum_le q G hFree l S hS
  have hPositive : positiveDeficiency q G l = signedDeficiency q G l := max_eq_left (by omega)
  rw [hPositive] at hFirst
  change (∑ w ∈ S, c w) ≤ _ at hFirst
  have hScaled := mul_le_mul_of_nonneg_left hFirst (show 0 ≤ 2 * (S.card : ℤ) by positivity)
  rw [hAllPairs] at hPairs
  linarith

/-- A sum of low-row positive entries is exactly the number of contributing rows. -/
theorem low_row_contribution_eq_card {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ v, G.degree v ≤ q + 2) (S : Finset (Fin n))
    (hLowS : ∀ w ∈ S, 1 ≤ signedDeficiency q G w) (v : Fin n) :
    (∑ w ∈ S, max (weightedResidual q G w v) 0) =
      ((S.filter fun w => v ∈ positivePartners q G w).card : ℤ) := by
  have hCount : ((S.filter fun w => v ∈ positivePartners q G w).card : ℤ) =
      ∑ w ∈ S, if v ∈ positivePartners q G w then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hCount]
  apply Finset.sum_congr rfl
  intro w hw
  have hBound := low_residual_entry_le_one q G hDegree w (hLowS w hw) v
  simp only [positivePartners, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

/-- The second-moment estimate in the original residual-entry representation. -/
theorem low_neighbor_residual_second_moment (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (S T : Finset (Fin (q ^ 2 + q + 2))) (hS : S ⊆ G.neighborFinset l)
    (hLowS : ∀ w ∈ S, 1 ≤ signedDeficiency q G w)
    (hT : ∀ v ∈ T, 0 ≤ signedDeficiency q G v) :
    (∑ v ∈ T, ((∑ w ∈ S, max (weightedResidual q G w v) 0) ^ 2 -
      (∑ w ∈ S, max (weightedResidual q G w v) 0))) ≤
      2 * (S.card : ℤ) ^ 2 + (∑ w ∈ S, signedDeficiency q G w) ^ 2 +
        2 * S.card * ((S.card : ℤ) * signedDeficiency q G l + ∑ y, positiveDeficiency q G y) := by
  simp_rw [low_row_contribution_eq_card q G hDegree S hLowS]
  exact low_neighbor_incidence_second_moment q G hFree hDegree l hLow S T hS hLowS hT

/-- Zero-codegree pairs among regular vertices have a weighted incidence bound. -/
theorem regular_set_missing_pair_bound (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (R : Finset (Fin (q ^ 2 + q + 2)))
    (hRegular : ∀ v ∈ R, signedDeficiency q G v = 0) :
    (∑ v ∈ R, (((zeroCodegreeGraph G).neighborFinset v ∩ R).card : ℤ)) ≤
      R.card + ∑ w, ((G.neighborFinset w ∩ R).card : ℤ) * positiveDeficiency q G w := by
  have hEach (v) (hv : v ∈ R) :
      (((zeroCodegreeGraph G).neighborFinset v ∩ R).card : ℤ) ≤
        1 + ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
    have hCard : (((zeroCodegreeGraph G).neighborFinset v ∩ R).card : ℤ) ≤
        (zeroCodegreeGraph G).degree v := by
      exact_mod_cast (show ((zeroCodegreeGraph G).neighborFinset v ∩ R).card ≤
        (zeroCodegreeGraph G).degree v by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
          Finset.card_le_card (Finset.inter_subset_left :
            (zeroCodegreeGraph G).neighborFinset v ∩ R ⊆ (zeroCodegreeGraph G).neighborFinset v))
    have hRow := zeroCodegree_degree_identity q G hFree v
    rw [hRegular v hv] at hRow
    have hWeights : (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) ≤
        ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    nlinarith
  have hSum := Finset.sum_le_sum hEach
  simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    sum_selected_neighbor_weights] using hSum

/-- Ordered pairs in a vertex set are either covered by a unique two-edge path or have zero codegree. -/
theorem pair_coverage_identity {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P : Finset (Fin n)) :
    (∑ v, (((G.neighborFinset v ∩ P).card : ℤ) ^ 2 - (G.neighborFinset v ∩ P).card)) +
      (∑ w ∈ P, (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ)) =
        (P.card : ℤ) * (P.card - 1) := by
  have hMoment := incidence_factorial_moment P Finset.univ (fun w => G.neighborFinset w)
  have hFilter (v : Fin n) : (P.filter fun w => v ∈ G.neighborFinset w) = G.neighborFinset v ∩ P := by
    ext w
    simp [G.neighborFinset_eq_filter, SimpleGraph.adj_comm, and_comm]
  simp_rw [hFilter] at hMoment
  simp only [Finset.univ_inter] at hMoment
  have hRow (w) (hw : w ∈ P) :
      (∑ u ∈ P.erase w, (codegree G w u : ℤ)) +
        (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ) = (P.card : ℤ) - 1 := by
    have hSets : ((P.erase w).filter fun u => codegree G w u = 0) =
        (zeroCodegreeGraph G).neighborFinset w ∩ P := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter,
        (zeroCodegreeGraph G).mem_neighborFinset]
      change ((u ≠ w ∧ u ∈ P) ∧ codegree G w u = 0) ↔
        ((w ≠ u ∧ codegree G w u = 0) ∧ u ∈ P)
      constructor
      · rintro ⟨⟨hNe, hP⟩, hZero⟩
        exact ⟨⟨hNe.symm, hZero⟩, hP⟩
      · rintro ⟨⟨hNe, hZero⟩, hP⟩
        exact ⟨⟨hNe.symm, hP⟩, hZero⟩
    have hZeroCount : (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ) =
        ∑ u ∈ P.erase w, if codegree G w u = 0 then 1 else 0 := by
      rw [← Finset.sum_filter, hSets]
      simp
    have hTerm (u) (hu : u ∈ P.erase w) :
        (codegree G w u : ℤ) + (if codegree G w u = 0 then 1 else 0) = 1 := by
      have hNe : w ≠ u := (Finset.mem_erase.mp hu).1.symm
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (codegree_le_one G hFree w u hNe) with h | h
      · simp [h]
      · simp [h]
    rw [hZeroCount, ← Finset.sum_add_distrib]
    have hCard : ((P.erase w).card : ℤ) + 1 = P.card := by exact_mod_cast Finset.card_erase_add_one hw
    rw [Finset.sum_congr rfl hTerm]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    omega
  calc
    _ = (∑ w ∈ P, ∑ u ∈ P.erase w, (codegree G w u : ℤ)) +
        ∑ w ∈ P, (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ) := by
      rw [hMoment]
      rfl
    _ = ∑ w ∈ P, ((∑ u ∈ P.erase w, (codegree G w u : ℤ)) +
        (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ)) := by rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_congr rfl hRow]
      simp
      ring

theorem restricted_pair_coverage_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P T : Finset (Fin n)) :
    (∑ v ∈ T, (((G.neighborFinset v ∩ P).card : ℤ) ^ 2 - (G.neighborFinset v ∩ P).card)) ≤
      (P.card : ℤ) * (P.card - 1) := by
  have hFull := pair_coverage_identity G hFree P
  have hMissing : 0 ≤ ∑ w ∈ P, (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ) := by
    positivity
  have hSubset :
      (∑ v ∈ T, (((G.neighborFinset v ∩ P).card : ℤ) ^ 2 - (G.neighborFinset v ∩ P).card)) ≤
        ∑ v, (((G.neighborFinset v ∩ P).card : ℤ) ^ 2 - (G.neighborFinset v ∩ P).card) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro v _ _
    have h := int_mul_pred_nonnegative ((G.neighborFinset v ∩ P).card : ℤ)
    nlinarith
  linarith

/-- A small family of centers has only a quadratic excess of incidences over the point count. -/
theorem sparse_family_incidence_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P C : Finset (Fin n)) :
    2 * (∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℤ)) ≤
      2 * P.card + (C.card : ℤ) * (C.card - 1) := by
  have hTerm (v : Fin n) : 2 * ((G.neighborFinset v ∩ C).card : ℤ) ≤
      2 + (((G.neighborFinset v ∩ C).card : ℤ) ^ 2 - (G.neighborFinset v ∩ C).card) := by
    have h := int_mul_pred_nonnegative (((G.neighborFinset v ∩ C).card : ℤ) - 1)
    nlinarith
  have hSum := Finset.sum_le_sum (fun v (_ : v ∈ P) => hTerm v)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hSum
  have hCoverage := restricted_pair_coverage_le G hFree C P
  have hIncidence : (∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℤ)) =
      ∑ w ∈ P, ((G.neighborFinset w ∩ C).card : ℤ) := by
    exact_mod_cast sum_neighbor_intersection_card G C P
  rw [hIncidence]
  nlinarith

def nonneighborCenters {n : ℕ} (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  Finset.univ.erase l \ G.neighborFinset l

def triangularNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  (G.neighborFinset l).filter fun w => codegree G l w = 1

def lowNeighbors {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  (G.neighborFinset l).filter fun w => 0 < signedDeficiency q G w

def blockChi {n : ℕ} (G : SimpleGraph (Fin n)) (l v : Fin n) : ℤ :=
  (if codegree G l v = 0 then 1 else 0) + (G.neighborFinset v ∩ triangularNeighbors G l).card

def blockEta {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l v : Fin n) : ℤ :=
  (G.neighborFinset v ∩ lowNeighbors q G l).card

def blockBaseline {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l v : Fin n) : ℤ :=
  signedDeficiency q G l - 1 + blockChi G l v + blockEta q G l v

theorem nonneighborCenters_spec {n : ℕ} (G : SimpleGraph (Fin n)) (l v : Fin n)
    (hv : v ∈ nonneighborCenters G l) : l ≠ v ∧ ¬G.Adj l v := by
  obtain ⟨hErase, hNot⟩ := Finset.mem_sdiff.mp hv
  refine ⟨(Finset.mem_erase.mp hErase).1.symm, ?_⟩
  exact fun h => hNot ((G.mem_neighborFinset l v).mpr h)

theorem nonneighborCenters_card (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (l : Fin (q ^ 2 + q + 2)) :
    ((nonneighborCenters G l).card : ℤ) = (q : ℤ) ^ 2 + signedDeficiency q G l := by
  have hSubset : G.neighborFinset l ⊆ Finset.univ.erase l := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset l w).mp hw).ne.symm, Finset.mem_univ _⟩
  have hCard : (nonneighborCenters G l).card + G.degree l = q ^ 2 + q + 1 := by
    simpa [nonneighborCenters, SimpleGraph.card_neighborFinset_eq_degree] using
      Finset.card_sdiff_add_card_eq_card hSubset
  have hCardInt : ((nonneighborCenters G l).card : ℤ) + G.degree l = (q : ℤ) ^ 2 + q + 1 := by
    exact_mod_cast hCard
  unfold signedDeficiency
  omega

theorem neighbor_subfamily_codegree_le {n : ℕ} (G : SimpleGraph (Fin n)) (l v : Fin n)
    (S : Finset (Fin n)) (hS : S ⊆ G.neighborFinset l) :
    (G.neighborFinset v ∩ S).card ≤ codegree G l v := by
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hwV, hwS⟩ := Finset.mem_inter.mp hw
  exact Finset.mem_inter.mpr ⟨hS hwS, hwV⟩

theorem block_indicator_bounds {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hv : v ∈ nonneighborCenters G l) :
    0 ≤ blockChi G l v ∧ blockChi G l v ≤ 1 ∧
      0 ≤ blockEta q G l v ∧ blockEta q G l v ≤ 1 := by
  have hNe := (nonneighborCenters_spec G l v hv).1
  have hCodegree := codegree_le_one G hFree l v hNe
  have hTri := neighbor_subfamily_codegree_le G l v (triangularNeighbors G l) (Finset.filter_subset _ _)
  have hLow := neighbor_subfamily_codegree_le G l v (lowNeighbors q G l) (Finset.filter_subset _ _)
  have hTriInt : ((G.neighborFinset v ∩ triangularNeighbors G l).card : ℤ) ≤ codegree G l v := by
    exact_mod_cast hTri
  have hLowInt : blockEta q G l v ≤ (codegree G l v : ℤ) := by
    unfold blockEta
    exact_mod_cast hLow
  have hCardInt : (codegree G l v : ℤ) ≤ 1 := by exact_mod_cast hCodegree
  have hTriNonneg : (0 : ℤ) ≤ (G.neighborFinset v ∩ triangularNeighbors G l).card := by positivity
  have hLowNonneg : 0 ≤ blockEta q G l v := by unfold blockEta; positivity
  by_cases hZero : codegree G l v = 0
  · simp only [blockChi, ite_eq_left hZero]
    rw [hZero] at hTriInt hLowInt
    norm_num at hTriInt hLowInt
    omega
  · have hOne : codegree G l v = 1 := by omega
    simp only [blockChi, ite_eq_right hZero, zero_add]
    rw [hOne] at hTriInt hLowInt
    norm_num at hTriInt hLowInt
    omega

theorem sum_neighbor_family_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (C P : Finset (Fin n)) (D : ℕ) (hDegree : ∀ w ∈ P, G.degree w ≤ D) :
    (∑ v ∈ C, (G.neighborFinset v ∩ P).card) ≤ D * P.card := by
  calc
    _ ≤ ∑ v, (G.neighborFinset v ∩ P).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ w ∈ P, G.degree w := by
      rw [sum_neighbor_intersection_card]
      simp
    _ ≤ ∑ _w ∈ P, D := Finset.sum_le_sum hDegree
    _ = _ := by simp [Nat.mul_comm]

theorem zero_codegree_centers_le_positivePartners {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l : Fin n) :
    (∑ v ∈ nonneighborCenters G l, if codegree G l v = 0 then (1 : ℤ) else 0) ≤
      (positivePartners q G l).card := by
  have hSubset : ((nonneighborCenters G l).filter fun v => codegree G l v = 0) ⊆
      positivePartners q G l := by
    intro v hv
    obtain ⟨hvCenter, hvZero⟩ := Finset.mem_filter.mp hv
    obtain ⟨hNe, hNot⟩ := nonneighborCenters_spec G l v hvCenter
    have hEntry := weightedResidual_nonadj q G l v hNe hNot
    rw [hvZero] at hEntry
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hEntry]⟩
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card hSubset

theorem blockChi_sum_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l : Fin n) :
    (∑ v ∈ nonneighborCenters G l, blockChi G l v) ≤
      (positivePartners q G l).card + ((q : ℤ) + 2) * (triangularNeighbors G l).card := by
  have hZero := zero_codegree_centers_le_positivePartners q G l
  have hTri : (∑ v ∈ nonneighborCenters G l,
      ((G.neighborFinset v ∩ triangularNeighbors G l).card : ℤ)) ≤
      ((q : ℤ) + 2) * (triangularNeighbors G l).card := by
    exact_mod_cast sum_neighbor_family_card_le G (nonneighborCenters G l) (triangularNeighbors G l)
      (q + 2) (fun w _ => hDegree w)
  simp only [blockChi, Finset.sum_add_distrib]
  linarith

theorem blockEta_sum_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    (∑ v ∈ nonneighborCenters G l, blockEta q G l v) ≤ (q : ℤ) * (lowNeighbors q G l).card := by
  have hDegree (w) (hw : w ∈ lowNeighbors q G l) : G.degree w ≤ q := by
    have hLow := (Finset.mem_filter.mp hw).2
    unfold signedDeficiency at hLow
    have hInt : (G.degree w : ℤ) ≤ q := by omega
    exact_mod_cast hInt
  unfold blockEta
  exact_mod_cast sum_neighbor_family_card_le G (nonneighborCenters G l) (lowNeighbors q G l) q hDegree

/-- The pair polynomial of a baseline with two binary increments. -/
theorem pair_polynomial_binary_add (F x y : ℤ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (F + x + y) * (F + x + y - 1) ≤ F * (F - 1) + 2 * F * x + 2 * (F + 1) * y := by
  have hxx : x * (x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 (by omega)
  have hyy : y * (y - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy0 (by omega)
  have hxy := mul_le_mul_of_nonneg_right hx1 hy0
  nlinarith

/-- Summing the baseline pair counts gives the explicit form of the manuscript's bound. -/
theorem blockBaseline_pair_sum_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) :
    (∑ v ∈ nonneighborCenters G l, blockBaseline q G l v * (blockBaseline q G l v - 1)) ≤
      ((q : ℤ) ^ 2 + signedDeficiency q G l) *
        (signedDeficiency q G l - 1) * (signedDeficiency q G l - 2) +
      2 * (signedDeficiency q G l - 1) *
        ((positivePartners q G l).card + ((q : ℤ) + 2) * (triangularNeighbors G l).card) +
      2 * signedDeficiency q G l * q * (lowNeighbors q G l).card := by
  have hPoint (v) (hv : v ∈ nonneighborCenters G l) :
      blockBaseline q G l v * (blockBaseline q G l v - 1) ≤
        (signedDeficiency q G l - 1) * (signedDeficiency q G l - 2) +
        2 * (signedDeficiency q G l - 1) * blockChi G l v +
        2 * signedDeficiency q G l * blockEta q G l v := by
    obtain ⟨hx0, hx1, hy0, hy1⟩ := block_indicator_bounds q G hFree l v hv
    have h := pair_polynomial_binary_add (signedDeficiency q G l - 1)
      (blockChi G l v) (blockEta q G l v) hx0 hx1 hy0 hy1
    unfold blockBaseline
    nlinarith
  have hSum := Finset.sum_le_sum hPoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hSum
  rw [nonneighborCenters_card] at hSum
  have hChi := mul_le_mul_of_nonneg_left (blockChi_sum_le q G hDegree l)
    (show 0 ≤ 2 * (signedDeficiency q G l - 1) by omega)
  have hEta := mul_le_mul_of_nonneg_left (blockEta_sum_le q G l)
    (show 0 ≤ 2 * signedDeficiency q G l by omega)
  nlinarith

theorem sum_common_triangle_codegrees {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) :
    (∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v, (codegree G l w : ℤ)) =
      (G.neighborFinset v ∩ triangularNeighbors G l).card := by
  have hTerm (w) (hw : w ∈ G.neighborFinset l ∩ G.neighborFinset v) :
      (codegree G l w : ℤ) = if codegree G l w = 1 then 1 else 0 := by
    have hAdj := (G.mem_neighborFinset l w).mp (Finset.mem_inter.mp hw).1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (codegree_le_one G hFree l w hAdj.ne) with h | h
    · simp [h]
    · simp [h]
  have hSets : ((G.neighborFinset l ∩ G.neighborFinset v).filter fun w => codegree G l w = 1) =
      G.neighborFinset v ∩ triangularNeighbors G l := by
    ext w
    simp [triangularNeighbors, and_assoc, and_comm]
  calc
    _ = ∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v,
        if codegree G l w = 1 then (1 : ℤ) else 0 := Finset.sum_congr rfl hTerm
    _ = _ := by rw [← Finset.sum_filter, hSets]; simp

theorem sum_common_low_indicators {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l v : Fin n) :
    (∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v,
      if 0 < signedDeficiency q G w then (1 : ℤ) else 0) =
      (G.neighborFinset v ∩ lowNeighbors q G l).card := by
  have hSets : ((G.neighborFinset l ∩ G.neighborFinset v).filter fun w =>
      0 < signedDeficiency q G w) = G.neighborFinset v ∩ lowNeighbors q G l := by
    ext w
    simp [lowNeighbors, and_assoc, and_comm]
  rw [← Finset.sum_filter, hSets]
  simp

/-- The binary baseline is the baseline in the verified pointwise block inequality. -/
theorem blockBaseline_eq {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hv : v ∈ nonneighborCenters G l) :
    blockBaseline q G l v = signedDeficiency q G l - (codegree G l v : ℤ) +
      ∑ w ∈ G.neighborFinset l ∩ G.neighborFinset v,
        ((codegree G l w : ℤ) + (if 0 < signedDeficiency q G w then 1 else 0)) := by
  have hNe := (nonneighborCenters_spec G l v hv).1
  have hZero : (if codegree G l v = 0 then (1 : ℤ) else 0) = 1 - (codegree G l v : ℤ) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (codegree_le_one G hFree l v hNe) with h | h
    · simp [h]
    · simp [h]
  rw [Finset.sum_add_distrib]
  unfold blockBaseline blockChi blockEta
  rw [hZero, ← sum_common_triangle_codegrees G hFree l v, ← sum_common_low_indicators q G l v]
  ring

theorem positive_row_block_bound_baseline {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hv : v ∈ nonneighborCenters G l)
    (hLow : 1 ≤ signedDeficiency q G l) (hNonhigh : 0 ≤ signedDeficiency q G v) :
    ((G.neighborFinset v ∩ positivePartners q G l).card : ℤ) ≤
      blockBaseline q G l v + ∑ w ∈ G.neighborFinset l, max (weightedResidual q G w v) 0 := by
  obtain ⟨hNe, hNot⟩ := nonneighborCenters_spec G l v hv
  have h := positive_row_block_bound q G hFree l v hNe hNot hLow hNonhigh
  rwa [← blockBaseline_eq q G hFree l v hv] at h

/-- Taking the positive part can only decrease this integer pair polynomial. -/
theorem pair_polynomial_posPart_le (D b : ℤ) :
    max (D - b) 0 * (max (D - b) 0 - 1) ≤ (D - b) * (D - b - 1) := by
  by_cases h : 0 ≤ D - b
  · rw [max_eq_left h]
  · have hNonpos : D - b ≤ 0 := le_of_not_ge h
    rw [max_eq_right hNonpos]
    simp only [zero_mul]
    exact int_mul_pred_nonnegative (D - b)

/-- The increase in pair count is charged only when the base count is exceeded. -/
theorem pair_polynomial_remainder_le (m t N : ℤ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hBound : m ≤ t + N) :
    m * (m - 1) ≤ t * (t - 1) + (if t < m then (m + t) * N else 0) := by
  by_cases h : t < m
  · rw [ite_eq_left h]
    have hDifference : m - t ≤ N := by omega
    have hProduct := mul_le_mul_of_nonneg_right hDifference (show 0 ≤ m + t by omega)
    nlinarith
  · rw [ite_eq_right h, add_zero]
    by_cases hZero : m = 0
    · rw [hZero]
      simp only [zero_mul]
      exact int_mul_pred_nonnegative t
    · have hProduct : 0 ≤ (t - m) * (t + m - 1) := mul_nonneg (by omega) (by omega)
      nlinarith

/-- Pair-count inequality with the low-point subtraction and a conditional error term. -/
theorem block_pair_count_bound (D b K R N m : ℤ) (hR : 0 ≤ R) (hm : 0 ≤ m)
    (hSmallBase : max (D - b) 0 ≤ K) (hBound : m ≤ max (D - b) 0 + R + N) :
    m * (m - 1) ≤ D * (D - 1) - 2 * (D - 1) * b + b * (b - 1) +
      2 * K * R + R * (R - 1) +
      (if max (D - b) 0 + R < m then (m + (max (D - b) 0 + R)) * N else 0) := by
  have hBase := pair_polynomial_posPart_le D b
  have hRemainder := pair_polynomial_remainder_le m (max (D - b) 0 + R) N hm
    (add_nonneg (le_max_right _ _) hR) hBound
  have hScaled := mul_le_mul_of_nonneg_right hSmallBase hR
  nlinarith

/-- At a small block, the conditional error is at most twice its threshold times N. -/
theorem block_pair_count_bound_of_small (D b K R N m t : ℤ) (hR : 0 ≤ R) (hN : 0 ≤ N)
    (hm : 0 ≤ m) (hThreshold : m ≤ t) (hSmallBase : max (D - b) 0 ≤ K)
    (hBound : m ≤ max (D - b) 0 + R + N) :
    m * (m - 1) ≤ D * (D - 1) - 2 * (D - 1) * b + b * (b - 1) +
      2 * K * R + R * (R - 1) + 2 * t * N := by
  have hMain := block_pair_count_bound D b K R N m hR hm hSmallBase hBound
  have hError : (if max (D - b) 0 + R < m then (m + (max (D - b) 0 + R)) * N else 0) ≤
      2 * t * N := by
    split_ifs with h
    · have hSum : m + (max (D - b) 0 + R) ≤ 2 * t := by omega
      nlinarith [mul_le_mul_of_nonneg_right hSum hN]
    · have ht : 0 ≤ t := hm.trans hThreshold
      positivity
  linarith

theorem disjoint_neighbor_blocks_card_le {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (A B P : Finset (Fin n)) (hDisjoint : Disjoint A B) (hA : A ⊆ P) (hB : B ⊆ P) :
    (G.neighborFinset v ∩ A).card + (G.neighborFinset v ∩ B).card ≤
      (G.neighborFinset v ∩ P).card := by
  have hIntersection : Disjoint (G.neighborFinset v ∩ A) (G.neighborFinset v ∩ B) :=
    hDisjoint.mono Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_union_of_disjoint hIntersection]
  apply Finset.card_le_card
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1, hA (Finset.mem_inter.mp hw).2⟩
  · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1, hB (Finset.mem_inter.mp hw).2⟩

/-- Disjoint point blocks inherit the baseline bound and its low and nonlow row contributions. -/
theorem positive_row_block_total_bound {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hv : v ∈ nonneighborCenters G l)
    (hLow : 1 ≤ signedDeficiency q G l) (hNonhigh : 0 ≤ signedDeficiency q G v)
    (A B : Finset (Fin n)) (hDisjoint : Disjoint A B)
    (hA : A ⊆ positivePartners q G l) (hB : B ⊆ positivePartners q G l) :
    ((G.neighborFinset v ∩ A).card : ℤ) + (G.neighborFinset v ∩ B).card ≤
      blockBaseline q G l v +
        (∑ w ∈ lowNeighbors q G l, max (weightedResidual q G w v) 0) +
        ∑ w ∈ G.neighborFinset l \ lowNeighbors q G l, max (weightedResidual q G w v) 0 := by
  have hCard : ((G.neighborFinset v ∩ A).card : ℤ) + (G.neighborFinset v ∩ B).card ≤
      (G.neighborFinset v ∩ positivePartners q G l).card := by
    exact_mod_cast disjoint_neighbor_blocks_card_le G v A B (positivePartners q G l) hDisjoint hA hB
  have hRaw := positive_row_block_bound_baseline q G hFree l v hv hLow hNonhigh
  have hSplit := Finset.sum_sdiff (f := fun w => max (weightedResidual q G w v) 0)
    (Finset.filter_subset (fun w => 0 < signedDeficiency q G w) (G.neighborFinset l))
  change (∑ w ∈ G.neighborFinset l \ lowNeighbors q G l, max (weightedResidual q G w v) 0) +
    (∑ w ∈ lowNeighbors q G l, max (weightedResidual q G w v) 0) =
    ∑ w ∈ G.neighborFinset l, max (weightedResidual q G w v) 0 at hSplit
  linarith

/-- The pair-count inequality applied to the graph's actual disjoint point blocks. -/
theorem positive_row_block_pair_bound {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hv : v ∈ nonneighborCenters G l)
    (hLow : 1 ≤ signedDeficiency q G l) (hNonhigh : 0 ≤ signedDeficiency q G v)
    (A B : Finset (Fin n)) (hDisjoint : Disjoint A B)
    (hA : A ⊆ positivePartners q G l) (hB : B ⊆ positivePartners q G l) :
    let D := blockBaseline q G l v
    let m : ℤ := (G.neighborFinset v ∩ A).card
    let b : ℤ := (G.neighborFinset v ∩ B).card
    let R := ∑ w ∈ lowNeighbors q G l, max (weightedResidual q G w v) 0
    let N := ∑ w ∈ G.neighborFinset l \ lowNeighbors q G l, max (weightedResidual q G w v) 0
    m * (m - 1) ≤ D * (D - 1) - 2 * (D - 1) * b + b * (b - 1) +
      2 * (signedDeficiency q G l + 1) * R + R * (R - 1) +
      (if max (D - b) 0 + R < m then (m + (max (D - b) 0 + R)) * N else 0) := by
  dsimp only
  apply block_pair_count_bound
  · exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  · positivity
  · obtain ⟨_, hChi, _, hEta⟩ := block_indicator_bounds q G hFree l v hv
    have hD : blockBaseline q G l v ≤ signedDeficiency q G l + 1 := by
      unfold blockBaseline
      omega
    have hCard : (0 : ℤ) ≤ (G.neighborFinset v ∩ B).card := by positivity
    apply max_le <;> omega
  · have hTotal := positive_row_block_total_bound q G hFree l v hv hLow hNonhigh A B hDisjoint hA hB
    have hMax := le_max_left
      (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0
    linarith

def lowNeighborContribution {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l v : Fin n) : ℤ :=
  ∑ w ∈ lowNeighbors q G l, max (weightedResidual q G w v) 0

def nonlowNeighborContribution {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l v : Fin n) : ℤ :=
  ∑ w ∈ G.neighborFinset l \ lowNeighbors q G l, max (weightedResidual q G w v) 0

theorem lowNeighborContribution_nonnegative {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l v : Fin n) :
    0 ≤ lowNeighborContribution q G l v := Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem nonlowNeighborContribution_nonnegative {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l v : Fin n) :
    0 ≤ nonlowNeighborContribution q G l v := Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem sum_lowNeighbors_deficiency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    (∑ w ∈ lowNeighbors q G l, signedDeficiency q G w) =
      ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w := by
  unfold lowNeighbors
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  unfold positiveDeficiency
  split_ifs <;> omega

theorem lowNeighborContribution_sum_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (T : Finset (Fin (q ^ 2 + q + 2))) :
    (∑ v ∈ T, lowNeighborContribution q G l v) ≤
      (q : ℤ) * (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) +
        (signedDeficiency q G l + 1) * (lowNeighbors q G l).card + ∑ y, positiveDeficiency q G y := by
  calc
    _ ≤ ∑ v, lowNeighborContribution q G l v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v _ _
      exact lowNeighborContribution_nonnegative q G l v
    _ = ∑ w ∈ lowNeighbors q G l, positiveResidualMass q G w := by
      unfold lowNeighborContribution
      rw [Finset.sum_comm]
      rfl
    _ ≤ _ := low_neighbor_positive_mass_sum_le q G hFree l hLow

theorem nonlowNeighborContribution_sum_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) (T : Finset (Fin (q ^ 2 + q + 2))) :
    (∑ v ∈ T, nonlowNeighborContribution q G l v) ≤
      signedDeficiency q G l * G.degree l + 3 * G.degree l + ∑ y, positiveDeficiency q G y := by
  have hSet : G.neighborFinset l \ lowNeighbors q G l =
      (G.neighborFinset l).filter fun w => signedDeficiency q G w ≤ 0 := by
    ext w
    by_cases hw : w ∈ G.neighborFinset l <;> simp [lowNeighbors, hw]
  calc
    _ ≤ ∑ v, nonlowNeighborContribution q G l v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v _ _
      exact nonlowNeighborContribution_nonnegative q G l v
    _ = ∑ w ∈ (G.neighborFinset l).filter (fun w => signedDeficiency q G w ≤ 0),
        positiveResidualMass q G w := by
      unfold nonlowNeighborContribution
      rw [Finset.sum_comm, hSet]
      rfl
    _ ≤ _ := nonlow_neighbor_positive_mass_sum_le q G hFree hDegree l hLow

theorem lowNeighborContribution_second_moment_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) (T : Finset (Fin (q ^ 2 + q + 2)))
    (hT : ∀ v ∈ T, 0 ≤ signedDeficiency q G v) :
    (∑ v ∈ T, (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v)) ≤
      2 * ((lowNeighbors q G l).card : ℤ) ^ 2 +
        (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) ^ 2 +
        2 * (lowNeighbors q G l).card *
          (((lowNeighbors q G l).card : ℤ) * signedDeficiency q G l + ∑ y, positiveDeficiency q G y) := by
  have hLowS (w) (hw : w ∈ lowNeighbors q G l) : 1 ≤ signedDeficiency q G w := by
    have h := (Finset.mem_filter.mp hw).2
    omega
  have h := low_neighbor_residual_second_moment q G hFree hDegree l hLow
    (lowNeighbors q G l) T (Finset.filter_subset _ _) hLowS hT
  rw [sum_lowNeighbors_deficiency] at h
  exact h

theorem positive_row_small_block_pair_bound {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l v : Fin n) (hv : v ∈ nonneighborCenters G l)
    (hLow : 1 ≤ signedDeficiency q G l) (hNonhigh : 0 ≤ signedDeficiency q G v)
    (A B : Finset (Fin n)) (hDisjoint : Disjoint A B)
    (hA : A ⊆ positivePartners q G l) (hB : B ⊆ positivePartners q G l)
    (t : ℤ) (hSmall : ((G.neighborFinset v ∩ A).card : ℤ) ≤ t) :
    let D := blockBaseline q G l v
    let m : ℤ := (G.neighborFinset v ∩ A).card
    let b : ℤ := (G.neighborFinset v ∩ B).card
    let R := lowNeighborContribution q G l v
    let N := nonlowNeighborContribution q G l v
    m ^ 2 - m ≤ D * (D - 1) - 2 * (D - 1) * b + (b ^ 2 - b) +
      2 * (signedDeficiency q G l + 1) * R + (R ^ 2 - R) + 2 * t * N := by
  have hBase : max (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0 ≤
      signedDeficiency q G l + 1 := by
    obtain ⟨_, hChi, _, hEta⟩ := block_indicator_bounds q G hFree l v hv
    have hD : blockBaseline q G l v ≤ signedDeficiency q G l + 1 := by
      unfold blockBaseline
      omega
    have hCard : (0 : ℤ) ≤ (G.neighborFinset v ∩ B).card := by positivity
    apply max_le <;> omega
  have hTotal := positive_row_block_total_bound q G hFree l v hv hLow hNonhigh A B hDisjoint hA hB
  have hMax := le_max_left (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0
  have hBound : ((G.neighborFinset v ∩ A).card : ℤ) ≤
      max (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0 +
        lowNeighborContribution q G l v + nonlowNeighborContribution q G l v := by
    change ((G.neighborFinset v ∩ A).card : ℤ) + (G.neighborFinset v ∩ B).card ≤
      blockBaseline q G l v + lowNeighborContribution q G l v + nonlowNeighborContribution q G l v at hTotal
    linarith
  have h := block_pair_count_bound_of_small (blockBaseline q G l v)
    ((G.neighborFinset v ∩ B).card : ℤ) (signedDeficiency q G l + 1)
    (lowNeighborContribution q G l v) (nonlowNeighborContribution q G l v)
    ((G.neighborFinset v ∩ A).card : ℤ) t
    (lowNeighborContribution_nonnegative q G l v) (nonlowNeighborContribution_nonnegative q G l v)
    (by positivity) hSmall hBase hBound
  dsimp only
  nlinarith

/-- Sum the small-block pair inequalities while preserving the low-point subtraction. -/
theorem small_block_pair_sum (q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l : Fin n) (hLow : 1 ≤ signedDeficiency q G l)
    (A B T : Finset (Fin n)) (hDisjoint : Disjoint A B)
    (hA : A ⊆ positivePartners q G l) (hB : B ⊆ positivePartners q G l)
    (hCenters : T ⊆ nonneighborCenters G l) (hNonhigh : ∀ v ∈ T, 0 ≤ signedDeficiency q G v)
    (t : ℤ) (hSmall : ∀ v ∈ T, ((G.neighborFinset v ∩ A).card : ℤ) ≤ t) :
    (∑ v ∈ T, (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) ≤
      (∑ v ∈ T, blockBaseline q G l v * (blockBaseline q G l v - 1)) -
      2 * (signedDeficiency q G l - 2) * (∑ v ∈ T, ((G.neighborFinset v ∩ B).card : ℤ)) +
      (∑ v ∈ T, (((G.neighborFinset v ∩ B).card : ℤ) ^ 2 - (G.neighborFinset v ∩ B).card)) +
      2 * (signedDeficiency q G l + 1) * (∑ v ∈ T, lowNeighborContribution q G l v) +
      (∑ v ∈ T, (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v)) +
      2 * t * (∑ v ∈ T, nonlowNeighborContribution q G l v) := by
  have hEach (v) (hv : v ∈ T) :
      ((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card ≤
        blockBaseline q G l v * (blockBaseline q G l v - 1) -
        2 * (signedDeficiency q G l - 2) * (G.neighborFinset v ∩ B).card +
        (((G.neighborFinset v ∩ B).card : ℤ) ^ 2 - (G.neighborFinset v ∩ B).card) +
        2 * (signedDeficiency q G l + 1) * lowNeighborContribution q G l v +
        (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v) +
        2 * t * nonlowNeighborContribution q G l v := by
    have h := positive_row_small_block_pair_bound q G hFree l v (hCenters hv) hLow
      (hNonhigh v hv) A B hDisjoint hA hB t (hSmall v hv)
    dsimp only at h
    obtain ⟨hChi, _, hEta, _⟩ := block_indicator_bounds q G hFree l v (hCenters hv)
    have hBase : signedDeficiency q G l - 1 ≤ blockBaseline q G l v := by
      unfold blockBaseline
      omega
    have hSubtraction := mul_le_mul_of_nonneg_right
      (show signedDeficiency q G l - 2 ≤ blockBaseline q G l v - 1 by omega)
      (show 0 ≤ 2 * ((G.neighborFinset v ∩ B).card : ℤ) by positivity)
    nlinarith
  have hSum := Finset.sum_le_sum hEach
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using hSum

/-- Explicit aggregate bound for a family of small nonhigh blocks. -/
theorem small_block_pair_sum_explicit (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l)
    (A B T : Finset (Fin (q ^ 2 + q + 2))) (hDisjoint : Disjoint A B)
    (hA : A ⊆ positivePartners q G l) (hB : B ⊆ positivePartners q G l)
    (hCenters : T ⊆ nonneighborCenters G l) (hNonhigh : ∀ v ∈ T, 0 ≤ signedDeficiency q G v)
    (t : ℤ) (ht : 0 ≤ t) (hSmall : ∀ v ∈ T, ((G.neighborFinset v ∩ A).card : ℤ) ≤ t) :
    let k := signedDeficiency q G l
    let d : ℤ := G.degree l
    let δ : ℤ := (lowNeighbors q G l).card
    let C := ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w
    let F := ∑ w, positiveDeficiency q G w
    let τ : ℤ := (triangularNeighbors G l).card
    let p : ℤ := (positivePartners q G l).card
    (∑ v ∈ T, (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) ≤
      ((q : ℤ) ^ 2 + k) * (k - 1) * (k - 2) + 2 * (k - 1) * (p + (q + 2) * τ) + 2 * k * q * δ -
      2 * (k - 2) * (∑ v ∈ T, ((G.neighborFinset v ∩ B).card : ℤ)) + (B.card : ℤ) * (B.card - 1) +
      2 * (k + 1) * (q * C + (k + 1) * δ + F) +
      (2 * δ ^ 2 + C ^ 2 + 2 * δ * (δ * k + F)) + 2 * t * (k * d + 3 * d + F) := by
  have hSum := small_block_pair_sum q G hFree l hLow A B T hDisjoint hA hB hCenters hNonhigh t hSmall
  have hBase : (∑ v ∈ T, blockBaseline q G l v * (blockBaseline q G l v - 1)) ≤
      ((q : ℤ) ^ 2 + signedDeficiency q G l) *
        (signedDeficiency q G l - 1) * (signedDeficiency q G l - 2) +
      2 * (signedDeficiency q G l - 1) *
        ((positivePartners q G l).card + ((q : ℤ) + 2) * (triangularNeighbors G l).card) +
      2 * signedDeficiency q G l * q * (lowNeighbors q G l).card := by
    calc
      _ ≤ ∑ v ∈ nonneighborCenters G l, blockBaseline q G l v * (blockBaseline q G l v - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hCenters
        intro v _ _
        exact int_mul_pred_nonnegative _
      _ ≤ _ := blockBaseline_pair_sum_le q G hFree hDegree l hLow
  have hBCount := restricted_pair_coverage_le G hFree B T
  have hL := lowNeighborContribution_sum_le q G hFree l hLow T
  have hLScaled := mul_le_mul_of_nonneg_left hL
    (show 0 ≤ 2 * (signedDeficiency q G l + 1) by omega)
  have hSecond := lowNeighborContribution_second_moment_le q G hFree hDegree l hLow T hNonhigh
  have hN := nonlowNeighborContribution_sum_le q G hFree hDegree l hLow T
  have hNScaled := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * t by omega)
  dsimp only
  nlinarith only [hSum, hBase, hBCount, hLScaled, hSecond, hNScaled]

/-- The uncovered pair demand is carried by centers outside a chosen small-block family. -/
theorem regular_set_remaining_pair_demand (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (A T : Finset (Fin (q ^ 2 + q + 2))) (hRegular : ∀ v ∈ A, signedDeficiency q G v = 0)
    (t : ℤ) (ht : 0 ≤ t) (hSmall : ∀ v ∈ T, ((G.neighborFinset v ∩ A).card : ℤ) ≤ t) :
    (A.card : ℤ) * (A.card - 1) ≤
      A.card + t * (∑ v, positiveDeficiency q G v) +
      (∑ v ∈ T, (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) +
      ∑ v ∈ Finset.univ \ T,
        (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card +
          (G.neighborFinset v ∩ A).card * positiveDeficiency q G v) := by
  have hCoverage := pair_coverage_identity G hFree A
  have hMissing := regular_set_missing_pair_bound q G hFree A hRegular
  have hSmallWeight : (∑ v ∈ T, ((G.neighborFinset v ∩ A).card : ℤ) * positiveDeficiency q G v) ≤
      t * (∑ v, positiveDeficiency q G v) := by
    calc
      _ ≤ ∑ v ∈ T, t * positiveDeficiency q G v := by
        apply Finset.sum_le_sum
        intro v hv
        exact mul_le_mul_of_nonneg_right (hSmall v hv) (positiveDeficiency_nonnegative q G v)
      _ = t * (∑ v ∈ T, positiveDeficiency q G v) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ ht
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _ _
        exact positiveDeficiency_nonnegative q G v
  have hSplitPairs := Finset.sum_sdiff
    (f := fun v => ((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)
    (Finset.subset_univ T)
  have hSplitWeights := Finset.sum_sdiff
    (f := fun v => ((G.neighborFinset v ∩ A).card : ℤ) * positiveDeficiency q G v)
    (Finset.subset_univ T)
  rw [Finset.sum_add_distrib]
  nlinarith only [hCoverage, hMissing, hSmallWeight, hSplitPairs, hSplitWeights]

/-- Zero-codegree neighbors contribute no three-edge walks to the other endpoint. -/
theorem threeWalkCount_add_block_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v l : Fin n) (hNot : ¬G.Adj v l)
    (P : Finset (Fin n)) (hZero : ∀ x ∈ P, codegree G l x = 0) :
    threeWalkCount G v l + (G.neighborFinset v ∩ P).card ≤ G.degree v := by
  have hCount : (G.neighborFinset v ∩ P).card =
      ∑ x ∈ G.neighborFinset v, if x ∈ P then 1 else 0 := by
    rw [← Finset.sum_filter]
    have hFilter : ((G.neighborFinset v).filter fun x => x ∈ P) = G.neighborFinset v ∩ P := by
      ext x
      simp
    rw [hFilter]
    simp
  have hEach (x) (hx : x ∈ G.neighborFinset v) :
      codegree G x l + (if x ∈ P then 1 else 0) ≤ 1 := by
    by_cases hxP : x ∈ P
    · have hZeros : codegree G x l = 0 := by rw [codegree_symm]; exact hZero x hxP
      simp only [hZeros, ite_eq_left hxP, zero_add, le_refl]
    · have hXL : x ≠ l := by
        intro h
        exact hNot (h ▸ (G.mem_neighborFinset v x).mp hx)
      simpa only [ite_eq_right hxP, add_zero] using codegree_le_one G hFree x l hXL
  calc
    _ = ∑ x ∈ G.neighborFinset v, (codegree G x l + (if x ∈ P then 1 else 0)) := by
      rw [Finset.sum_add_distrib, ← hCount]
      rfl
    _ ≤ ∑ _x ∈ G.neighborFinset v, 1 := Finset.sum_le_sum hEach
    _ = _ := by simp

/-- A nonempty block on nonhigh positive partners has a nonedge as its center pair. -/
theorem nonempty_positive_block_nonedge {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l v : Fin n) (hLow : 1 ≤ signedDeficiency q G l) (P : Finset (Fin n))
    (hP : P ⊆ positivePartners q G l) (hNonhigh : ∀ x ∈ P, 0 ≤ signedDeficiency q G x)
    (hNonempty : 0 < (G.neighborFinset v ∩ P).card) : l ≠ v ∧ ¬G.Adj l v := by
  have hNot : ¬(v = l ∨ G.Adj l v) := by
    intro h
    have hEmpty := nonhigh_positive_block_empty q G l hLow P hP hNonhigh v h
    rw [hEmpty] at hNonempty
    simp at hNonempty
  exact ⟨fun h => hNot (Or.inl h.symm), fun h => hNot (Or.inr h)⟩

/-- The no-cheap-edge hypothesis leaves a fixed gap in every nonempty positive block. -/
theorem no_cheap_edge_block_degree_gap (q C : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l v : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ positivePartners q G l)
    (hNonhigh : ∀ x ∈ P, 0 ≤ signedDeficiency q G x)
    (hNonempty : 0 < (G.neighborFinset v ∩ P).card)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    q + 8 * C * (G.neighborFinset v ∩ P).card ≤ 8 * C * G.degree v := by
  obtain ⟨hNe, hNot⟩ := nonempty_positive_block_nonedge q G l v hLow P hP hNonhigh hNonempty
  have hNotRev : ¬G.Adj v l := fun h => hNot h.symm
  have hZeros (x) (hx : x ∈ P) : codegree G l x = 0 :=
    (positivePartner_nonhigh q G l x hLow (hNonhigh x hx) (hP hx)).2.2
  have hWalk := threeWalkCount_add_block_le G hFree v l hNotRev P hZeros
  have hLower := hNoCheap v l hNe.symm hNotRev
  have hUpper := Nat.mul_le_mul_left C (withEdge_copyCount_le G hFree v l hNe.symm)
  have hScaled := Nat.mul_le_mul_left (8 * C) hWalk
  nlinarith

theorem degree_add_positiveDeficiency_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ x, G.degree x ≤ q + 2) (v : Fin n) :
    (G.degree v : ℤ) + positiveDeficiency q G v ≤ (q : ℤ) + 2 := by
  have hUpper : (G.degree v : ℤ) ≤ (q : ℤ) + 2 := by exact_mod_cast hDegree v
  by_cases hNonnegative : 0 ≤ signedDeficiency q G v
  · unfold positiveDeficiency
    rw [max_eq_left hNonnegative]
    unfold signedDeficiency
    omega
  · unfold positiveDeficiency
    rw [max_eq_right (le_of_not_ge hNonnegative)]
    omega

theorem no_cheap_edge_weighted_block_gap (q C : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2)
    (l v : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ positivePartners q G l)
    (hNonhigh : ∀ x ∈ P, 0 ≤ signedDeficiency q G x)
    (hNonempty : 0 < (G.neighborFinset v ∩ P).card)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    (q : ℤ) + 8 * C * (((G.neighborFinset v ∩ P).card : ℤ) + positiveDeficiency q G v) ≤
      8 * C * ((q : ℤ) + 2) := by
  have hGap : (q : ℤ) + 8 * C * (G.neighborFinset v ∩ P).card ≤ 8 * C * G.degree v := by
    exact_mod_cast no_cheap_edge_block_degree_gap q C G hFree l v hLow P hP hNonhigh hNonempty hNoCheap
  have hDegreeGap := degree_add_positiveDeficiency_le q G hDegree v
  have hScaled := mul_le_mul_of_nonneg_left hDegreeGap (show 0 ≤ 8 * (C : ℤ) by positivity)
  nlinarith

/-- The block-size gap also bounds the weighted pair coverage of any selected center family. -/
theorem no_cheap_edge_weighted_pair_sum_le (q C : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) (P T : Finset (Fin (q ^ 2 + q + 2)))
    (hP : P ⊆ positivePartners q G l) (hNonhigh : ∀ x ∈ P, 0 ≤ signedDeficiency q G x)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    (8 * (C : ℤ)) * (∑ v ∈ T,
        (((G.neighborFinset v ∩ P).card : ℤ) ^ 2 - (G.neighborFinset v ∩ P).card +
          (G.neighborFinset v ∩ P).card * positiveDeficiency q G v)) ≤
      (8 * C * ((q : ℤ) + 1) - q) * (∑ v ∈ T, ((G.neighborFinset v ∩ P).card : ℤ)) := by
  have hEach (v) (_hv : v ∈ T) :
      (8 * (C : ℤ)) *
          (((G.neighborFinset v ∩ P).card : ℤ) ^ 2 - (G.neighborFinset v ∩ P).card +
            (G.neighborFinset v ∩ P).card * positiveDeficiency q G v) ≤
        (8 * C * ((q : ℤ) + 1) - q) * (G.neighborFinset v ∩ P).card := by
    by_cases hEmpty : (G.neighborFinset v ∩ P).card = 0
    · simp [hEmpty]
    · have hNonempty : 0 < (G.neighborFinset v ∩ P).card := by omega
      have hGap := no_cheap_edge_weighted_block_gap q C G hFree hDegree l v hLow P hP
        hNonhigh hNonempty hNoCheap
      have hScaled := mul_le_mul_of_nonneg_right hGap
        (Nat.cast_nonneg (α := ℤ) (G.neighborFinset v ∩ P).card)
      nlinarith
  have hSum := Finset.sum_le_sum hEach
  simpa only [← Finset.mul_sum] using hSum

def regularPositivePartners {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  (positivePartners q G l).filter fun v => signedDeficiency q G v = 0

def lowPositivePartners {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  (positivePartners q G l).filter fun v => 0 < signedDeficiency q G v

def highPositivePartners {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  positivePartners q G l ∩ highVertices q G

theorem mem_highVertices_iff {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    v ∈ highVertices q G ↔ signedDeficiency q G v < 0 := by
  simp only [highVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold signedDeficiency
  omega

/-- Above degree q+1, the q+2 cap leaves exactly one unit of negative deficiency. -/
theorem positiveDeficiency_eq_signed_add_high {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ v, G.degree v ≤ q + 2) (v : Fin n) :
    positiveDeficiency q G v = signedDeficiency q G v + (if v ∈ highVertices q G then 1 else 0) := by
  have hLower := signedDeficiency_ge_neg_one q G hDegree v
  simp only [mem_highVertices_iff]
  unfold positiveDeficiency
  by_cases h : signedDeficiency q G v < 0
  · rw [ite_eq_left h, max_eq_right (le_of_lt h)]
    omega
  · rw [ite_eq_right h, max_eq_left (le_of_not_gt h)]
    omega

theorem sum_positiveDeficiency_eq_signed_add_high {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ v, G.degree v ≤ q + 2) (S : Finset (Fin n)) :
    (∑ v ∈ S, positiveDeficiency q G v) =
      (∑ v ∈ S, signedDeficiency q G v) + (S ∩ highVertices q G).card := by
  have hCount : ((S ∩ highVertices q G).card : ℤ) =
      ∑ v ∈ S, if v ∈ highVertices q G then 1 else 0 := by
    rw [← Finset.sum_filter]
    have hFilter : (S.filter fun v => v ∈ highVertices q G) = S ∩ highVertices q G := by
      ext v
      simp
    rw [hFilter]
    simp
  simp_rw [positiveDeficiency_eq_signed_add_high q G hDegree]
  rw [Finset.sum_add_distrib, ← hCount]

theorem total_positiveDeficiency_eq_signed_add_high {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ v, G.degree v ≤ q + 2) :
    (∑ v, positiveDeficiency q G v) =
      (∑ v, signedDeficiency q G v) + (highVertices q G).card := by
  simpa only [Finset.univ_inter] using sum_positiveDeficiency_eq_signed_add_high q G hDegree Finset.univ

/-- Positive partners split into regular, low, and high vertices. -/
theorem positive_partner_partition_card {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    (regularPositivePartners q G l).card + (lowPositivePartners q G l).card +
      (highPositivePartners q G l).card = (positivePartners q G l).card := by
  have hA : (regularPositivePartners q G l).card =
      ∑ v ∈ positivePartners q G l, if signedDeficiency q G v = 0 then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp [regularPositivePartners]
  have hB : (lowPositivePartners q G l).card =
      ∑ v ∈ positivePartners q G l, if 0 < signedDeficiency q G v then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp [lowPositivePartners]
  have hH : (highPositivePartners q G l).card =
      ∑ v ∈ positivePartners q G l, if v ∈ highVertices q G then 1 else 0 := by
    rw [← Finset.sum_filter]
    have hFilter : ((positivePartners q G l).filter fun v => v ∈ highVertices q G) =
        highPositivePartners q G l := by
      ext v
      simp [highPositivePartners]
    rw [hFilter]
    simp
  have hTerm (v : Fin n) :
      (if signedDeficiency q G v = 0 then (1 : ℕ) else 0) +
        (if 0 < signedDeficiency q G v then 1 else 0) +
        (if v ∈ highVertices q G then 1 else 0) = 1 := by
    simp only [mem_highVertices_iff]
    split_ifs <;> omega
  rw [hA, hB, hH, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp_rw [hTerm]
  simp

theorem regular_low_positivePartners_disjoint {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    Disjoint (regularPositivePartners q G l) (lowPositivePartners q G l) := by
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  have hZero := (Finset.mem_filter.mp hvA).2
  have hPositive := (Finset.mem_filter.mp hvB).2
  omega

theorem highPositivePartners_card_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    (highPositivePartners q G l).card ≤ (highVertices q G).card :=
  Finset.card_le_card Finset.inter_subset_right

theorem triangle_codegree_sum_eq_card {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l : Fin n) :
    (∑ w ∈ G.neighborFinset l, (codegree G l w : ℤ)) = (triangularNeighbors G l).card := by
  have h := sum_common_triangle_codegrees G hFree l l
  have hSubset : triangularNeighbors G l ⊆ G.neighborFinset l := Finset.filter_subset _ _
  simpa only [Finset.inter_self, Finset.inter_eq_right.mpr hSubset] using h

theorem neighbor_positiveDeficiency_le_signed_add_high {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hDegree : ∀ v, G.degree v ≤ q + 2) (l : Fin n) :
    (∑ v ∈ G.neighborFinset l, positiveDeficiency q G v) ≤
      (∑ v ∈ G.neighborFinset l, signedDeficiency q G v) + (highVertices q G).card := by
  have h := sum_positiveDeficiency_eq_signed_add_high q G hDegree (G.neighborFinset l)
  have hCard : ((G.neighborFinset l ∩ highVertices q G).card : ℤ) ≤ (highVertices q G).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right :
      G.neighborFinset l ∩ highVertices q G ⊆ highVertices q G)
  omega

/-- The regular positive-row size is determined up to the bounded high-vertex error. -/
theorem regular_positivePartners_card_bounds (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) :
    (signedDeficiency q G l - 1) * q + signedDeficiency q G l +
        (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) + (triangularNeighbors G l).card -
        (lowPositivePartners q G l).card - 2 * (highVertices q G).card ≤
      ((regularPositivePartners q G l).card : ℤ) ∧
    ((regularPositivePartners q G l).card : ℤ) ≤
      (signedDeficiency q G l - 1) * q + signedDeficiency q G l +
        (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) + (triangularNeighbors G l).card -
        (lowPositivePartners q G l).card := by
  have hLower := low_positivePartners_card_lower q G hFree hDegree l hLow
  have hUpper := low_positivePartners_card_upper q G hFree l hLow
  rw [triangle_codegree_sum_eq_card G hFree l] at hLower hUpper
  have hPartition : ((regularPositivePartners q G l).card : ℤ) + (lowPositivePartners q G l).card +
      (highPositivePartners q G l).card = (positivePartners q G l).card := by
    exact_mod_cast positive_partner_partition_card q G l
  have hHigh : ((highPositivePartners q G l).card : ℤ) ≤ (highVertices q G).card := by
    exact_mod_cast highPositivePartners_card_le q G l
  have hHighNonnegative : (0 : ℤ) ≤ (highPositivePartners q G l).card := by positivity
  have hWeights := neighbor_positiveDeficiency_le_signed_add_high q G hDegree l
  constructor <;> linarith

theorem dense_positiveDeficiency_le_high_card (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card) :
    (∑ v, positiveDeficiency q G v) ≤ 2 * (q : ℤ) + (highVertices q G).card - 4 := by
  rw [total_positiveDeficiency_eq_signed_add_high q G hDegree]
  have h := dense_total_deficiency_le q G hDense
  omega

theorem neighbor_positiveDeficiency_le_total {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    (∑ v ∈ G.neighborFinset l, positiveDeficiency q G v) ≤ ∑ v, positiveDeficiency q G v := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro v _ _
  exact positiveDeficiency_nonnegative q G v

theorem lowPositivePartners_card_le_total {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    ((lowPositivePartners q G l).card : ℤ) ≤ ∑ v, positiveDeficiency q G v := by
  have hEach (v) (hv : v ∈ lowPositivePartners q G l) : (1 : ℤ) ≤ positiveDeficiency q G v := by
    have h := (Finset.mem_filter.mp hv).2
    unfold positiveDeficiency
    omega
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hSum
  have hSubset : (∑ v ∈ lowPositivePartners q G l, positiveDeficiency q G v) ≤
      ∑ v, positiveDeficiency q G v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro v _ _
    exact positiveDeficiency_nonnegative q G v
  exact hSum.trans hSubset

/-- Exact total incidences into a prescribed point set. -/
theorem neighbor_family_incidence_eq {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) :
    (∑ v, ((G.neighborFinset v ∩ B).card : ℤ)) =
      ((q : ℤ) + 1) * B.card - ∑ w ∈ B, signedDeficiency q G w := by
  have hCount : (∑ v, ((G.neighborFinset v ∩ B).card : ℤ)) =
      ∑ w ∈ B, (G.degree w : ℤ) := by
    have h := sum_neighbor_intersection_card G Finset.univ B
    simp only [Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree] at h
    exact_mod_cast h
  rw [hCount]
  have hTerm (w) : (G.degree w : ℤ) = (q : ℤ) + 1 - signedDeficiency q G w := by
    unfold signedDeficiency
    ring
  simp_rw [hTerm]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

theorem neighbor_family_incidence_lower {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) :
    ((q : ℤ) + 1) * B.card - (∑ w, positiveDeficiency q G w) ≤
      ∑ v, ((G.neighborFinset v ∩ B).card : ℤ) := by
  have hPositive : (∑ w ∈ B, signedDeficiency q G w) ≤ ∑ w, positiveDeficiency q G w := by
    calc
      _ ≤ ∑ w ∈ B, positiveDeficiency q G w := Finset.sum_le_sum (fun _ _ => le_max_left _ _)
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro w _ _
        exact positiveDeficiency_nonnegative q G w
  rw [neighbor_family_incidence_eq q G B]
  linarith

theorem nonneighborCenters_mem_iff {n : ℕ} (G : SimpleGraph (Fin n)) (l v : Fin n) :
    v ∈ nonneighborCenters G l ↔ v ≠ l ∧ ¬G.Adj l v := by
  simp [nonneighborCenters, G.mem_neighborFinset]

/-- Nonhigh positive partners have no incidences at the excluded centers. -/
theorem nonneighbor_positive_incidence_eq_total {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l : Fin n) (hLow : 1 ≤ signedDeficiency q G l) (B : Finset (Fin n))
    (hB : B ⊆ positivePartners q G l) (hNonhigh : ∀ w ∈ B, 0 ≤ signedDeficiency q G w) :
    (∑ v ∈ nonneighborCenters G l, ((G.neighborFinset v ∩ B).card : ℤ)) =
      ∑ v, ((G.neighborFinset v ∩ B).card : ℤ) := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  have hCenter : v = l ∨ G.Adj l v := by
    by_cases h : v = l
    · exact Or.inl h
    · apply Or.inr
      by_contra hNot
      exact hv ((nonneighborCenters_mem_iff G l v).mpr ⟨h, hNot⟩)
  have hEmpty := nonhigh_positive_block_empty q G l hLow B hB hNonhigh v hCenter
  simp [hEmpty]

/-- A bound for incidences at a selected set of exceptional centers. -/
theorem selected_center_incidence_le {n : ℕ} (G : SimpleGraph (Fin n))
    (B H : Finset (Fin n)) (D : ℕ) (hDegree : ∀ v ∈ H, G.degree v ≤ D) :
    (∑ v ∈ H, ((G.neighborFinset v ∩ B).card : ℤ)) ≤ (D : ℤ) * H.card := by
  have hEach (v) (hv : v ∈ H) : ((G.neighborFinset v ∩ B).card : ℤ) ≤ D := by
    exact_mod_cast (show (G.neighborFinset v ∩ B).card ≤ D from
      (Finset.card_le_card Finset.inter_subset_left).trans
        (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hDegree v hv))
  have hSum := Finset.sum_le_sum hEach
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hSum

/-- Removing two sets of centers loses at most the sum of their individual contributions. -/
theorem sum_remove_union_le {ι : Type*} [DecidableEq ι]
    (C R H : Finset ι) (a : ι → ℤ) (ha : ∀ v, 0 ≤ a v) :
    (∑ v ∈ C, a v) ≤ (∑ v ∈ C \ (R ∪ H), a v) + (∑ v ∈ R, a v) + ∑ v ∈ H, a v := by
  have hSplit := Finset.sum_sdiff (f := a) (Finset.inter_subset_left : C ∩ (R ∪ H) ⊆ C)
  have hSets : C \ (C ∩ (R ∪ H)) = C \ (R ∪ H) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hSets] at hSplit
  have hIntersection : (∑ v ∈ C ∩ (R ∪ H), a v) ≤ ∑ v ∈ R ∪ H, a v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    intro v _ _
    exact ha v
  have hUnion := Finset.sum_union_inter (s₁ := R) (s₂ := H) (f := a)
  have hNonnegative : 0 ≤ ∑ v ∈ R ∩ H, a v := Finset.sum_nonneg (fun v _ => ha v)
  linarith

/-- The retained nonhigh centers contain almost q incidences per low positive partner. -/
theorem retained_positive_incidence_lower (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) (B R : Finset (Fin (q ^ 2 + q + 2)))
    (hB : B ⊆ positivePartners q G l) (hNonhigh : ∀ w ∈ B, 0 ≤ signedDeficiency q G w) :
    2 * (q : ℤ) * B.card - 2 * (∑ w, positiveDeficiency q G w) -
      (R.card : ℤ) * (R.card - 1) - 2 * ((q : ℤ) + 2) * (highVertices q G).card ≤
      2 * (∑ v ∈ nonneighborCenters G l \ (R ∪ highVertices q G),
        ((G.neighborFinset v ∩ B).card : ℤ)) := by
  have hTotal := neighbor_family_incidence_lower q G B
  rw [← nonneighbor_positive_incidence_eq_total q G l hLow B hB hNonhigh] at hTotal
  have hRemoval := sum_remove_union_le (nonneighborCenters G l) R (highVertices q G)
    (fun v => ((G.neighborFinset v ∩ B).card : ℤ)) (fun _ => by positivity)
  have hLarge := sparse_family_incidence_bound G hFree B R
  have hHigh := selected_center_incidence_le G B (highVertices q G) (q + 2)
    (fun v _ => hDegree v)
  push_cast at hHigh
  nlinarith

def growingLocalLower (q k c b τ h L : ℤ) : ℤ :=
  L * ((k - 1) ^ 2 * q ^ 2 + 2 * (k - 1) * q * (k + c + τ - b - 2 * h) -
    ((k - 1) * q + k + c + τ - b))

def growingLocalUpper (q k c b τ h δ L : ℤ) : ℤ :=
  L * ((q ^ 2 + k) * (k - 1) * (k - 2) +
    2 * (k - 1) * (((k - 1) * q + k + c + τ) + (q + 2) * τ) + 2 * k * q * δ) -
  2 * L * (k - 2) * (q * b - (2 * q + h) - h * (q + 2)) + L * b * (b - 1) +
  2 * L * (k + 1) * (q * c + (k + 1) * δ + (2 * q + h)) +
  L * (2 * δ ^ 2 + c ^ 2 + 2 * δ * (δ * k + (2 * q + h))) +
  ((L - 1) * q + L * (k + δ + 3)) * (k * (q + 1 - k) + 3 * (q + 1 - k) + (2 * q + h)) +
  L * (h * (q + 2) ^ 2 + ((k - 1) * q + k + c + τ - b) + (2 * q + h) * (q + 2))

/-- The leading difference in the growing-deficiency comparison. -/
theorem growing_local_difference_identity (q k c b τ h δ L : ℤ) :
    growingLocalLower q k c b τ h L - growingLocalUpper q k c b τ h δ L =
      k * q * (q - k) +
      (2 * L * h * q + L * k + 4 * L * τ + 3 * L * b + 6 * L * k ^ 2 + L * h +
        5 * q ^ 2 + 3 * q + h * q) -
      (L * (8 * q ^ 2 + 6 * h * k * q + 14 * k * q + 4 * c * q + 2 * b * q +
        18 * q + 2 * c * k + 6 * k * τ + 9 * h * k + b ^ 2 + c ^ 2 + 9 + h * q ^ 2) + 2 * k * q) -
      L * δ * (3 * k * q + k ^ 2 + 2 * k + 5 + 9 * q + 3 * h) -
      2 * L * δ ^ 2 * (1 + k) := by
  unfold growingLocalLower growingLocalUpper
  ring

theorem growing_local_constant_error_le (q k c b τ h L : ℤ)
    (hq : 1 ≤ q) (hL : 1 ≤ L) (hh : 0 ≤ h) (hhq : h ≤ q)
    (hk : 1 ≤ k) (hkq : k ≤ q + 1) (hc : 0 ≤ c) (hcq : c ≤ 2 * q + h)
    (hb : 0 ≤ b) (hbq : b ≤ 2 * q + h) (hτ : 0 ≤ τ) (hτq : τ ≤ q + 2) :
    L * (8 * q ^ 2 + 6 * h * k * q + 14 * k * q + 4 * c * q + 2 * b * q +
      18 * q + 2 * c * k + 6 * k * τ + 9 * h * k + b ^ 2 + c ^ 2 + 9 + h * q ^ 2) + 2 * k * q ≤
      200 * L * (h + 1) * q ^ 2 := by
  have hk2 : k ≤ 2 * q := by omega
  have hc3 : c ≤ 3 * q := by omega
  have hb3 : b ≤ 3 * q := by omega
  have hτ3 : τ ≤ 3 * q := by omega
  have hqSquare : q ≤ q ^ 2 := by nlinarith [int_mul_pred_nonnegative q]
  have hqSquareOne : 1 ≤ q ^ 2 := by nlinarith
  have hkqBound : k * q ≤ 2 * q ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hk2 (show 0 ≤ q by omega)]
  have hcqBound : c * q ≤ 3 * q ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hc3 (show 0 ≤ q by omega)]
  have hbqBound : b * q ≤ 3 * q ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hb3 (show 0 ≤ q by omega)]
  have hckBound : c * k ≤ 6 * q ^ 2 := by
    nlinarith [mul_le_mul hc3 hk2 (show 0 ≤ k by omega) (show 0 ≤ 3 * q by omega)]
  have hkτBound : k * τ ≤ 6 * q ^ 2 := by
    nlinarith [mul_le_mul hk2 hτ3 hτ (show 0 ≤ 2 * q by omega)]
  have hbSquare : b ^ 2 ≤ 9 * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * q - b by omega) (show 0 ≤ 3 * q + b by omega)]
  have hcSquare : c ^ 2 ≤ 9 * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * q - c by omega) (show 0 ≤ 3 * q + c by omega)]
  have hBase : 8 * q ^ 2 + 14 * k * q + 4 * c * q + 2 * b * q + 18 * q +
      2 * c * k + 6 * k * τ + b ^ 2 + c ^ 2 + 9 ≤ 147 * q ^ 2 := by
    nlinarith only [hkqBound, hcqBound, hbqBound, hqSquare, hqSquareOne, hckBound, hkτBound, hbSquare, hcSquare]
  have hHKQ := mul_le_mul_of_nonneg_left hkqBound hh
  have hHK := mul_le_mul_of_nonneg_left hk2 hh
  have hHQ := mul_le_mul_of_nonneg_left hqSquare hh
  have hHPart : 6 * h * k * q + 9 * h * k + h * q ^ 2 ≤ 31 * h * q ^ 2 := by
    nlinarith only [hHKQ, hHK, hHQ]
  have hBaseL := mul_le_mul_of_nonneg_left hBase (show 0 ≤ L by omega)
  have hHPartL := mul_le_mul_of_nonneg_left hHPart (show 0 ≤ L by omega)
  have hLQ := mul_le_mul_of_nonneg_right hL (sq_nonneg q)
  have hLH : 0 ≤ L * h * q ^ 2 := by positivity
  nlinarith only [hBaseL, hHPartL, hkqBound, hLQ, hLH]

theorem growing_local_delta_error_le (q k h δ L : ℤ)
    (hq : 1 ≤ q) (hL : 1 ≤ L) (hhq : h ≤ q)
    (hk : 1 ≤ k) (hkq : k ≤ q + 1) (hδ : 0 ≤ δ) (hδq : δ ≤ q) :
    L * δ * (3 * k * q + k ^ 2 + 2 * k + 5 + 9 * q + 3 * h) +
      2 * L * δ ^ 2 * (1 + k) ≤ 30 * L * δ * k * q := by
  have hk2 : k ≤ 2 * q := by omega
  have hkSquare : k ^ 2 ≤ 2 * k * q := by
    nlinarith [mul_le_mul_of_nonneg_left hk2 (show 0 ≤ k by omega)]
  have hkq : k ≤ k * q := by nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ q - 1 by omega)]
  have hqk : q ≤ k * q := by nlinarith [mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ k - 1 by omega)]
  have hOne : 1 ≤ k * q := by nlinarith
  have hCoefficient : 3 * k * q + k ^ 2 + 2 * k + 5 + 9 * q + 3 * h ≤ 24 * k * q := by
    nlinarith only [hkSquare, hkq, hqk, hOne, hhq]
  have hLinear := mul_le_mul_of_nonneg_left hCoefficient (show 0 ≤ L * δ by positivity)
  have hDeltaSquare : δ ^ 2 ≤ δ * q := by nlinarith [mul_nonneg hδ (show 0 ≤ q - δ by omega)]
  have hKplus : 1 + k ≤ 2 * k := by omega
  have hKplusScaled := mul_le_mul_of_nonneg_left hKplus (show 0 ≤ 2 * L * δ ^ 2 by positivity)
  have hDeltaScaled := mul_le_mul_of_nonneg_left hDeltaSquare (show 0 ≤ 4 * L * k by positivity)
  have hPadding : 0 ≤ L * δ * k * q := by positivity
  nlinarith only [hLinear, hKplusScaled, hDeltaScaled, hPadding]

theorem growing_local_difference_lower (q k c b τ h δ L : ℤ)
    (hq : 1 ≤ q) (hL : 1 ≤ L) (hh : 0 ≤ h) (hhq : h ≤ q)
    (hk : 1 ≤ k) (hkq : k ≤ q + 1) (hc : 0 ≤ c) (hcq : c ≤ 2 * q + h)
    (hb : 0 ≤ b) (hbq : b ≤ 2 * q + h) (hτ : 0 ≤ τ) (hτq : τ ≤ q + 2)
    (hδ : 0 ≤ δ) (hδq : δ ≤ q) :
    k * q * (q - k) - 30 * L * δ * k * q - 200 * L * (h + 1) * q ^ 2 ≤
      growingLocalLower q k c b τ h L - growingLocalUpper q k c b τ h δ L := by
  have hConstant := growing_local_constant_error_le q k c b τ h L hq hL hh hhq hk hkq hc hcq hb hbq hτ hτq
  have hDelta := growing_local_delta_error_le q k h δ L hq hL hhq hk hkq hδ hδq
  have hPositive : 0 ≤ 2 * L * h * q + L * k + 4 * L * τ + 3 * L * b + 6 * L * k ^ 2 +
      L * h + 5 * q ^ 2 + 3 * q + h * q := by positivity
  rw [growing_local_difference_identity]
  nlinarith only [hConstant, hDelta, hPositive]

/-- A numerical contradiction for large local deficiency and few low neighbors. -/
theorem growing_local_numeric_contradiction (q k c b τ h δ L : ℤ)
    (hq : 1 ≤ q) (hL : 1 ≤ L) (hh : 0 ≤ h) (hhq : h ≤ q)
    (hk : 1 ≤ k) (hkq : k ≤ q + 1) (hc : 0 ≤ c) (hcq : c ≤ 2 * q + h)
    (hb : 0 ≤ b) (hbq : b ≤ 2 * q + h) (hτ : 0 ≤ τ) (hτq : τ ≤ q + 2)
    (hδ : 0 ≤ δ) (hδq : δ ≤ q) (hGap : q ≤ 4 * L * (q - k))
    (hFew : 240 * L ^ 2 * δ ≤ q) (hLarge : 1601 * L ^ 2 * (h + 1) ≤ k)
    (hCompare : growingLocalLower q k c b τ h L ≤ growingLocalUpper q k c b τ h δ L) : False := by
  have hLower := growing_local_difference_lower q k c b τ h δ L hq hL hh hhq hk hkq hc hcq hb hbq hτ hτq hδ hδq
  have hScaled := mul_le_mul_of_nonneg_left hLower (show 0 ≤ 8 * L by omega)
  have hCompareScaled := mul_le_mul_of_nonneg_left hCompare (show 0 ≤ 8 * L by omega)
  have hGapScaled := mul_le_mul_of_nonneg_right hGap (show 0 ≤ 2 * k * q by positivity)
  have hFewScaled := mul_le_mul_of_nonneg_right hFew (show 0 ≤ k * q by positivity)
  have hLargeScaled := mul_le_mul_of_nonneg_right hLarge (sq_nonneg q)
  have hPositive : 0 < L ^ 2 * (h + 1) * q ^ 2 := by positivity
  nlinarith only [hScaled, hCompareScaled, hGapScaled, hFewScaled, hLargeScaled, hPositive]

theorem lowNeighborContribution_le_card (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hDegree : ∀ w, G.degree w ≤ q + 2)
    (l v : Fin (q ^ 2 + q + 2)) :
    lowNeighborContribution q G l v ≤ (lowNeighbors q G l).card := by
  have hEach (w) (hw : w ∈ lowNeighbors q G l) : max (weightedResidual q G w v) 0 ≤ 1 := by
    have hLow : 1 ≤ signedDeficiency q G w := by
      have h := (Finset.mem_filter.mp hw).2
      omega
    exact max_le (low_residual_entry_le_one q G hDegree w hLow v) (by norm_num)
  have hSum := Finset.sum_le_sum hEach
  simpa only [lowNeighborContribution, Finset.sum_const, nsmul_eq_mul, mul_one] using hSum

def nonhighNonneighborCenters {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l : Fin n) : Finset (Fin n) := nonneighborCenters G l \ highVertices q G

theorem nonhighNonneighborCenters_spec {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (l v : Fin n) (hv : v ∈ nonhighNonneighborCenters q G l) :
    v ∈ nonneighborCenters G l ∧ 0 ≤ signedDeficiency q G v := by
  obtain ⟨hCenter, hNotHigh⟩ := Finset.mem_sdiff.mp hv
  exact ⟨hCenter, le_of_not_gt (fun h => hNotHigh ((mem_highVertices_iff q G v).mpr h))⟩

/-- The no-cheap-edge gap controls the pair-count error without a size threshold. -/
theorem block_pair_error_scaled_le (q C : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l v : Fin (q ^ 2 + q + 2))
    (hv : v ∈ nonneighborCenters G l) (hLow : 1 ≤ signedDeficiency q G l)
    (A B : Finset (Fin (q ^ 2 + q + 2))) (hA : A ⊆ positivePartners q G l)
    (hNonhighA : ∀ w ∈ A, 0 ≤ signedDeficiency q G w)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    let L : ℤ := 8 * C
    let m : ℤ := (G.neighborFinset v ∩ A).card
    let b : ℤ := (G.neighborFinset v ∩ B).card
    let s := max (blockBaseline q G l v - b) 0
    let R := lowNeighborContribution q G l v
    let N := nonlowNeighborContribution q G l v
    L * (if s + R < m then (m + (s + R)) * N else 0) ≤
      ((L - 1) * q + L * (signedDeficiency q G l + (lowNeighbors q G l).card + 3)) * N := by
  dsimp only
  let L : ℤ := 8 * C
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hR := lowNeighborContribution_le_card q G hDegree l v
  have hN := nonlowNeighborContribution_nonnegative q G l v
  obtain ⟨_, hChi, _, hEta⟩ := block_indicator_bounds q G hFree l v hv
  have hD : blockBaseline q G l v ≤ signedDeficiency q G l + 1 := by
    unfold blockBaseline
    omega
  have hs : max (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0 ≤
      signedDeficiency q G l + 1 := by
    have hb : (0 : ℤ) ≤ (G.neighborFinset v ∩ B).card := by positivity
    apply max_le <;> omega
  by_cases hTrigger : max (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0 +
      lowNeighborContribution q G l v < ((G.neighborFinset v ∩ A).card : ℤ)
  · rw [ite_eq_left hTrigger]
    have hPositive : 0 < (G.neighborFinset v ∩ A).card := by
      have hRNonnegative := lowNeighborContribution_nonnegative q G l v
      have hsNonnegative := le_max_right (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0
      have hPos : (0 : ℤ) < (G.neighborFinset v ∩ A).card := by omega
      exact_mod_cast hPos
    have hGap := no_cheap_edge_weighted_block_gap q C G hFree hDegree l v hLow A hA hNonhighA hPositive hNoCheap
    have hF := positiveDeficiency_nonnegative q G v
    have hLF : 0 ≤ L * positiveDeficiency q G v := mul_nonneg (by omega) hF
    have hsScaled := mul_le_mul_of_nonneg_left hs (show 0 ≤ L by omega)
    have hRScaled := mul_le_mul_of_nonneg_left hR (show 0 ≤ L by omega)
    have hSum : L * (((G.neighborFinset v ∩ A).card : ℤ) +
        (max (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0 + lowNeighborContribution q G l v)) ≤
        (L - 1) * q + L * (signedDeficiency q G l + (lowNeighbors q G l).card + 3) := by
      change (q : ℤ) + L * (((G.neighborFinset v ∩ A).card : ℤ) + positiveDeficiency q G v) ≤
        L * ((q : ℤ) + 2) at hGap
      nlinarith
    have hProduct := mul_le_mul_of_nonneg_right hSum hN
    change L * _ ≤ _
    nlinarith only [hProduct]
  · rw [ite_eq_right hTrigger, mul_zero]
    have hCoefficient : 0 ≤ (L - 1) * q + L * (signedDeficiency q G l + (lowNeighbors q G l).card + 3) := by
      positivity
    exact mul_nonneg hCoefficient hN

/-- Aggregate pair counts over all selected nonhigh centers using the fixed block gap. -/
theorem nonhigh_scaled_block_pair_sum (q C : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ w, G.degree w ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) (A B T : Finset (Fin (q ^ 2 + q + 2)))
    (hDisjoint : Disjoint A B) (hA : A ⊆ positivePartners q G l) (hB : B ⊆ positivePartners q G l)
    (hNonhighA : ∀ w ∈ A, 0 ≤ signedDeficiency q G w)
    (hCenters : T ⊆ nonneighborCenters G l) (hNonhighT : ∀ v ∈ T, 0 ≤ signedDeficiency q G v)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    let L : ℤ := 8 * C
    L * (∑ v ∈ T, (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) ≤
      L * (∑ v ∈ T, blockBaseline q G l v * (blockBaseline q G l v - 1)) -
      2 * L * (signedDeficiency q G l - 2) * (∑ v ∈ T, ((G.neighborFinset v ∩ B).card : ℤ)) +
      L * (∑ v ∈ T, (((G.neighborFinset v ∩ B).card : ℤ) ^ 2 - (G.neighborFinset v ∩ B).card)) +
      2 * L * (signedDeficiency q G l + 1) * (∑ v ∈ T, lowNeighborContribution q G l v) +
      L * (∑ v ∈ T, (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v)) +
      ((L - 1) * q + L * (signedDeficiency q G l + (lowNeighbors q G l).card + 3)) *
        (∑ v ∈ T, nonlowNeighborContribution q G l v) := by
  let L : ℤ := 8 * C
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hEach (v) (hv : v ∈ T) :
      L * (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card) ≤
        L * (blockBaseline q G l v * (blockBaseline q G l v - 1)) -
        2 * L * (signedDeficiency q G l - 2) * (G.neighborFinset v ∩ B).card +
        L * (((G.neighborFinset v ∩ B).card : ℤ) ^ 2 - (G.neighborFinset v ∩ B).card) +
        2 * L * (signedDeficiency q G l + 1) * lowNeighborContribution q G l v +
        L * (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v) +
        ((L - 1) * q + L * (signedDeficiency q G l + (lowNeighbors q G l).card + 3)) *
          nonlowNeighborContribution q G l v := by
    have hPoint := positive_row_block_pair_bound q G hFree l v (hCenters hv) hLow (hNonhighT v hv)
      A B hDisjoint hA hB
    have hError := block_pair_error_scaled_le q C hC G hFree hDegree l v (hCenters hv) hLow A B hA hNonhighA hNoCheap
    change ((G.neighborFinset v ∩ A).card : ℤ) * ((G.neighborFinset v ∩ A).card - 1) ≤
      blockBaseline q G l v * (blockBaseline q G l v - 1) -
      2 * (blockBaseline q G l v - 1) * (G.neighborFinset v ∩ B).card +
      ((G.neighborFinset v ∩ B).card : ℤ) * ((G.neighborFinset v ∩ B).card - 1) +
      2 * (signedDeficiency q G l + 1) * lowNeighborContribution q G l v +
      lowNeighborContribution q G l v * (lowNeighborContribution q G l v - 1) +
      (if max (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0 + lowNeighborContribution q G l v <
          (G.neighborFinset v ∩ A).card then
        (((G.neighborFinset v ∩ A).card : ℤ) +
          (max (blockBaseline q G l v - ((G.neighborFinset v ∩ B).card : ℤ)) 0 + lowNeighborContribution q G l v)) *
            nonlowNeighborContribution q G l v else 0) at hPoint
    change L * _ ≤ _ at hError
    have hScaled := mul_le_mul_of_nonneg_left hPoint hL
    obtain ⟨hChi, _, hEta, _⟩ := block_indicator_bounds q G hFree l v (hCenters hv)
    have hBase : signedDeficiency q G l - 2 ≤ blockBaseline q G l v - 1 := by
      unfold blockBaseline
      omega
    have hSubtraction := mul_le_mul_of_nonneg_right hBase
      (show 0 ≤ 2 * L * ((G.neighborFinset v ∩ B).card : ℤ) by positivity)
    nlinarith only [hScaled, hError, hSubtraction]
  have hSum := Finset.sum_le_sum hEach
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using hSum

/-- High centers and zero-codegree pairs account for only the displayed quadratic loss. -/
theorem regular_positive_block_pair_demand_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) (A : Finset (Fin (q ^ 2 + q + 2)))
    (hA : A ⊆ positivePartners q G l) (hRegular : ∀ v ∈ A, signedDeficiency q G v = 0) :
    (A.card : ℤ) * (A.card - 1) ≤
      (∑ v ∈ nonhighNonneighborCenters q G l,
        (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) +
      (highVertices q G).card * ((q : ℤ) + 2) ^ 2 + A.card +
      ((q : ℤ) + 2) * (∑ v, positiveDeficiency q G v) := by
  let T := nonhighNonneighborCenters q G l
  have hBlock (v) : ((G.neighborFinset v ∩ A).card : ℤ) ≤ (q : ℤ) + 2 := by
    exact_mod_cast (show (G.neighborFinset v ∩ A).card ≤ q + 2 from
      (Finset.card_le_card Finset.inter_subset_left).trans
        (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hDegree v))
  have hDemand := regular_set_remaining_pair_demand q G hFree A T hRegular ((q : ℤ) + 2)
    (by positivity) (fun v _ => hBlock v)
  have hEach (v) (hv : v ∈ Finset.univ \ T) :
      ((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card +
        (G.neighborFinset v ∩ A).card * positiveDeficiency q G v ≤
      if v ∈ highVertices q G then ((q : ℤ) + 2) ^ 2 else 0 := by
    by_cases hHigh : v ∈ highVertices q G
    · have hNegative := (mem_highVertices_iff q G v).mp hHigh
      have hZero : positiveDeficiency q G v = 0 := max_eq_right (le_of_lt hNegative)
      rw [ite_eq_left hHigh, hZero, mul_zero, add_zero]
      have hM := hBlock v
      have hNonnegative : (0 : ℤ) ≤ (G.neighborFinset v ∩ A).card := by positivity
      have hProduct := mul_nonneg (show 0 ≤ (q : ℤ) + 2 - (G.neighborFinset v ∩ A).card by omega)
        (show 0 ≤ (q : ℤ) + 2 + (G.neighborFinset v ∩ A).card by positivity)
      nlinarith
    · have hNotCenter : v ∉ nonneighborCenters G l := by
        intro hCenter
        exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨hCenter, hHigh⟩)
      have hCase : v = l ∨ G.Adj l v := by
        by_cases hEqual : v = l
        · exact Or.inl hEqual
        · apply Or.inr
          by_contra hNot
          exact hNotCenter ((nonneighborCenters_mem_iff G l v).mpr ⟨hEqual, hNot⟩)
      have hEmpty := nonhigh_positive_block_empty q G l hLow A hA
        (fun w hw => by rw [hRegular w hw]) v hCase
      simp [hHigh, hEmpty]
  have hSum := Finset.sum_le_sum hEach
  have hExtend : (∑ v ∈ Finset.univ \ T,
      if v ∈ highVertices q G then ((q : ℤ) + 2) ^ 2 else 0) ≤
      ∑ v, if v ∈ highVertices q G then ((q : ℤ) + 2) ^ 2 else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro v _ _
    split_ifs <;> positivity
  have hCount : (∑ v, if v ∈ highVertices q G then ((q : ℤ) + 2) ^ 2 else 0) =
      (highVertices q G).card * ((q : ℤ) + 2) ^ 2 := by
    rw [← Finset.sum_filter]
    simp
  rw [hCount] at hExtend
  change (A.card : ℤ) * (A.card - 1) ≤ _
  nlinarith only [hDemand, hSum, hExtend]

/-- The graph estimates imply the numerical comparison used in the growing-deficiency case. -/
theorem growing_graph_comparison (q C : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (l : Fin (q ^ 2 + q + 2)) (hK : 2 ≤ signedDeficiency q G l)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    let k := signedDeficiency q G l
    let c := ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w
    let b : ℤ := (lowPositivePartners q G l).card
    let τ : ℤ := (triangularNeighbors G l).card
    let h : ℤ := (highVertices q G).card
    let δ : ℤ := (lowNeighbors q G l).card
    let L : ℤ := 8 * C
    growingLocalLower q k c b τ h L ≤ growingLocalUpper q k c b τ h δ L := by
  let A := regularPositivePartners q G l
  let B := lowPositivePartners q G l
  let T := nonhighNonneighborCenters q G l
  let k := signedDeficiency q G l
  let c := ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w
  let b : ℤ := B.card
  let τ : ℤ := (triangularNeighbors G l).card
  let h : ℤ := (highVertices q G).card
  let δ : ℤ := (lowNeighbors q G l).card
  let L : ℤ := 8 * C
  let F := ∑ w, positiveDeficiency q G w
  let p : ℤ := (positivePartners q G l).card
  let m : ℤ := A.card
  let pBound := (k - 1) * q + k + c + τ
  let fBound := 2 * (q : ℤ) + h
  let Q := (L - 1) * q + L * (k + δ + 3)
  have hLow : 1 ≤ k := by dsimp [k]; omega
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hQ : 0 ≤ Q := by
    have hL1 : 1 ≤ L := by dsimp [L]; omega
    dsimp [Q]
    positivity
  have hA : A ⊆ positivePartners q G l := Finset.filter_subset _ _
  have hB : B ⊆ positivePartners q G l := Finset.filter_subset _ _
  have hRegA (v) (hv : v ∈ A) : signedDeficiency q G v = 0 := (Finset.mem_filter.mp hv).2
  have hNonA (v) (hv : v ∈ A) : 0 ≤ signedDeficiency q G v := by rw [hRegA v hv]
  have hNonB (v) (hv : v ∈ B) : 0 ≤ signedDeficiency q G v := by
    have hPositive := (Finset.mem_filter.mp hv).2
    omega
  have hDisjoint : Disjoint A B := regular_low_positivePartners_disjoint q G l
  have hCenters : T ⊆ nonneighborCenters G l := Finset.sdiff_subset
  have hNonT (v) (hv : v ∈ T) : 0 ≤ signedDeficiency q G v :=
    (nonhighNonneighborCenters_spec q G l v hv).2
  have hF : F ≤ fBound := by
    have hSharp := dense_positiveDeficiency_le_high_card q G hDegree hDense
    change F ≤ fBound - 4 at hSharp
    omega
  have hRows := regular_positivePartners_card_bounds q G hFree hDegree l hLow
  change pBound - b - 2 * h ≤ m ∧ m ≤ pBound - b at hRows
  have hP : p ≤ pBound := by
    have hUpper := low_positivePartners_card_upper q G hFree l hLow
    rw [triangle_codegree_sum_eq_card G hFree l] at hUpper
    exact hUpper
  have hD : (G.degree l : ℤ) = (q : ℤ) + 1 - k := by
    dsimp [k]
    unfold signedDeficiency
    ring
  have hBaseRaw : (∑ v ∈ T, blockBaseline q G l v * (blockBaseline q G l v - 1)) ≤
      ((q : ℤ) ^ 2 + k) * (k - 1) * (k - 2) +
        2 * (k - 1) * (p + ((q : ℤ) + 2) * τ) + 2 * k * q * δ := by
    calc
      _ ≤ ∑ v ∈ nonneighborCenters G l, blockBaseline q G l v * (blockBaseline q G l v - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hCenters
        intro v _ _
        exact int_mul_pred_nonnegative _
      _ ≤ _ := blockBaseline_pair_sum_le q G hFree hDegree l hLow
  have hPScaled := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2 * (k - 1) by omega)
  have hBase : (∑ v ∈ T, blockBaseline q G l v * (blockBaseline q G l v - 1)) ≤
      ((q : ℤ) ^ 2 + k) * (k - 1) * (k - 2) +
        2 * (k - 1) * (pBound + ((q : ℤ) + 2) * τ) + 2 * k * q * δ := by
    nlinarith only [hBaseRaw, hPScaled]
  have hBaseScaled := mul_le_mul_of_nonneg_left hBase hL
  have hIncRaw := retained_positive_incidence_lower q G hFree hDegree l hLow B ∅ hB hNonB
  simp only [Finset.empty_union, Finset.card_empty, Nat.cast_zero, zero_mul, sub_zero] at hIncRaw
  change 2 * (q : ℤ) * b - 2 * F - 2 * ((q : ℤ) + 2) * h ≤
    2 * (∑ v ∈ T, ((G.neighborFinset v ∩ B).card : ℤ)) at hIncRaw
  have hInc : (q : ℤ) * b - fBound - h * ((q : ℤ) + 2) ≤
      ∑ v ∈ T, ((G.neighborFinset v ∩ B).card : ℤ) := by nlinarith only [hIncRaw, hF]
  have hIncScaled := mul_le_mul_of_nonneg_left hInc (show 0 ≤ 2 * L * (k - 2) by positivity)
  have hPairs := restricted_pair_coverage_le G hFree B T
  change (∑ v ∈ T, (((G.neighborFinset v ∩ B).card : ℤ) ^ 2 - (G.neighborFinset v ∩ B).card)) ≤ b * (b - 1) at hPairs
  have hPairsScaled := mul_le_mul_of_nonneg_left hPairs hL
  have hLowFirst := lowNeighborContribution_sum_le q G hFree l hLow T
  change (∑ v ∈ T, lowNeighborContribution q G l v) ≤ (q : ℤ) * c + (k + 1) * δ + F at hLowFirst
  have hLowFirstBound : (∑ v ∈ T, lowNeighborContribution q G l v) ≤
      (q : ℤ) * c + (k + 1) * δ + fBound := by linarith
  have hLowFirstScaled := mul_le_mul_of_nonneg_left hLowFirstBound (show 0 ≤ 2 * L * (k + 1) by positivity)
  have hLowSecond := lowNeighborContribution_second_moment_le q G hFree hDegree l hLow T hNonT
  change (∑ v ∈ T, (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v)) ≤
    2 * δ ^ 2 + c ^ 2 + 2 * δ * (δ * k + F) at hLowSecond
  have hFScaled := mul_le_mul_of_nonneg_left hF (show 0 ≤ 2 * δ by positivity)
  have hLowSecondBound : (∑ v ∈ T, (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v)) ≤
      2 * δ ^ 2 + c ^ 2 + 2 * δ * (δ * k + fBound) := by nlinarith only [hLowSecond, hFScaled]
  have hLowSecondScaled := mul_le_mul_of_nonneg_left hLowSecondBound hL
  have hNonlow := nonlowNeighborContribution_sum_le q G hFree hDegree l hLow T
  change (∑ v ∈ T, nonlowNeighborContribution q G l v) ≤ k * G.degree l + 3 * G.degree l + F at hNonlow
  rw [hD] at hNonlow
  have hNonlowBound : (∑ v ∈ T, nonlowNeighborContribution q G l v) ≤
      k * ((q : ℤ) + 1 - k) + 3 * ((q : ℤ) + 1 - k) + fBound := by linarith
  have hNonlowScaled := mul_le_mul_of_nonneg_left hNonlowBound hQ
  have hAggregate := nonhigh_scaled_block_pair_sum q C hC G hFree hDegree l hLow A B T
    hDisjoint hA hB hNonA hCenters hNonT hNoCheap
  change L * (∑ v ∈ T, (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) ≤
      L * (∑ v ∈ T, blockBaseline q G l v * (blockBaseline q G l v - 1)) -
      2 * L * (k - 2) * (∑ v ∈ T, ((G.neighborFinset v ∩ B).card : ℤ)) +
      L * (∑ v ∈ T, (((G.neighborFinset v ∩ B).card : ℤ) ^ 2 - (G.neighborFinset v ∩ B).card)) +
      2 * L * (k + 1) * (∑ v ∈ T, lowNeighborContribution q G l v) +
      L * (∑ v ∈ T, (lowNeighborContribution q G l v ^ 2 - lowNeighborContribution q G l v)) +
      Q * (∑ v ∈ T, nonlowNeighborContribution q G l v) at hAggregate
  have hUpper : L * (∑ v ∈ T,
      (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) ≤
      growingLocalUpper q k c b τ h δ L -
        L * (h * ((q : ℤ) + 2) ^ 2 + (pBound - b) + fBound * ((q : ℤ) + 2)) := by
    unfold growingLocalUpper
    dsimp only [pBound, fBound, Q] at hBaseScaled hIncScaled hLowFirstScaled hLowSecondScaled hNonlowScaled hAggregate ⊢
    nlinarith only [hAggregate, hBaseScaled, hIncScaled, hPairsScaled, hLowFirstScaled, hLowSecondScaled, hNonlowScaled]
  have hCoverage := regular_positive_block_pair_demand_le q G hFree hDegree l hLow A hA hRegA
  change m * (m - 1) ≤
    (∑ v ∈ T, (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) +
    h * ((q : ℤ) + 2) ^ 2 + m + ((q : ℤ) + 2) * F at hCoverage
  have hCoverageScaled := mul_le_mul_of_nonneg_left hCoverage hL
  have hMScaled := mul_le_mul_of_nonneg_left hRows.2 hL
  have hFCoverageScaled := mul_le_mul_of_nonneg_left hF (show 0 ≤ L * ((q : ℤ) + 2) by positivity)
  have hUpperTotal : L * (m * (m - 1)) ≤ growingLocalUpper q k c b τ h δ L := by
    nlinarith only [hUpper, hCoverageScaled, hMScaled, hFCoverageScaled]
  have hTangent := sq_nonneg (m - (k - 1) * q)
  have hRowsScaled := mul_le_mul_of_nonneg_left hRows.1 (show 0 ≤ 2 * (k - 1) * q by positivity)
  have hLowerRaw : (k - 1) ^ 2 * (q : ℤ) ^ 2 +
      2 * (k - 1) * q * (k + c + τ - b - 2 * h) - (pBound - b) ≤ m * (m - 1) := by
    dsimp only [pBound] at hRowsScaled hRows ⊢
    nlinarith only [hTangent, hRowsScaled, hRows.2]
  have hLowerScaled := mul_le_mul_of_nonneg_left hLowerRaw hL
  change growingLocalLower q k c b τ h L ≤ growingLocalUpper q k c b τ h δ L
  unfold growingLocalLower
  dsimp only [pBound] at hLowerScaled
  exact hLowerScaled.trans hUpperTotal

/-- Large deficiency forces a positive fraction of low neighbors, uniformly in its growth rate. -/
theorem growing_deficiency_forces_low_neighbors (q C : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hq : 32 * C ≤ q) (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (l : Fin (q ^ 2 + q + 2))
    (hLarge : 1601 * (8 * (C : ℤ)) ^ 2 * ((highVertices q G).card + 1) ≤ signedDeficiency q G l) :
    (q : ℤ) < 240 * (8 * (C : ℤ)) ^ 2 * (lowNeighbors q G l).card := by
  let k := signedDeficiency q G l
  let c := ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w
  let b : ℤ := (lowPositivePartners q G l).card
  let τ : ℤ := (triangularNeighbors G l).card
  let h : ℤ := (highVertices q G).card
  let δ : ℤ := (lowNeighbors q G l).card
  let L : ℤ := 8 * C
  change 1601 * L ^ 2 * (h + 1) ≤ k at hLarge
  change (q : ℤ) < 240 * L ^ 2 * δ
  have hq8 : 8 ≤ q := by omega
  have hqInt : (1 : ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hhq : h ≤ q := by dsimp [h]; exact_mod_cast hHigh
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hHProduct := mul_le_mul_of_nonneg_left (show 1 ≤ h + 1 by omega) (sq_nonneg L)
  have hk : 2 ≤ k := by nlinarith only [hLarge, hLsq, hHProduct]
  have hkq : k ≤ (q : ℤ) + 1 := by dsimp [k]; unfold signedDeficiency; omega
  have hc : 0 ≤ c := Finset.sum_nonneg (fun w _ => positiveDeficiency_nonnegative q G w)
  have hF := dense_positiveDeficiency_le_high_card q G hDegree hDense
  have hcTotal := neighbor_positiveDeficiency_le_total q G l
  have hcq : c ≤ 2 * (q : ℤ) + h := by
    change c ≤ _ at hcTotal
    change _ ≤ 2 * (q : ℤ) + h - 4 at hF
    linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbTotal := lowPositivePartners_card_le_total q G l
  have hbq : b ≤ 2 * (q : ℤ) + h := by
    change b ≤ _ at hbTotal
    linarith
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτDegree : τ ≤ G.degree l := by
    dsimp [τ]
    exact_mod_cast (show (triangularNeighbors G l).card ≤ G.degree l by
      simpa only [triangularNeighbors, SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (Finset.filter_subset (fun w => codegree G l w = 1) (G.neighborFinset l)))
  have hτq : τ ≤ (q : ℤ) + 2 := by
    have hCap : (G.degree l : ℤ) ≤ (q : ℤ) + 2 := by exact_mod_cast hDegree l
    omega
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδDegree : δ ≤ G.degree l := by
    dsimp [δ]
    exact_mod_cast (show (lowNeighbors q G l).card ≤ G.degree l by
      simpa only [lowNeighbors, SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (Finset.filter_subset (fun w => 0 < signedDeficiency q G w) (G.neighborFinset l)))
  have hDegreeEq : (G.degree l : ℤ) = (q : ℤ) + 1 - k := by
    dsimp [k]
    unfold signedDeficiency
    ring
  have hδq : δ ≤ q := by omega
  have hMin := degree_lower_of_no_cheap_edge q C hq8 G hFree hDense hNoCheap l
  have hMinInt : (q : ℤ) ≤ (16 * (C : ℤ)) * G.degree l := by exact_mod_cast hMin
  rw [hDegreeEq] at hMinInt
  have hqScale : (32 : ℤ) * C ≤ q := by exact_mod_cast hq
  have hGap : (q : ℤ) ≤ 4 * L * (q - k) := by
    dsimp [L]
    nlinarith only [hMinInt, hqScale]
  have hCompare := growing_graph_comparison q C hC G hFree hDegree hDense l hk hNoCheap
  change growingLocalLower q k c b τ h L ≤ growingLocalUpper q k c b τ h δ L at hCompare
  by_contra hNot
  have hFew : 240 * L ^ 2 * δ ≤ (q : ℤ) := by omega
  exact growing_local_numeric_contradiction q k c b τ h δ L hqInt hL hh hhq (by omega) hkq
    hc hcq hb hbq hτ hτq hδ hδq hGap hFew hLarge hCompare

theorem regular_neighbor_card_lower {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    (G.degree l : ℤ) - (lowNeighbors q G l).card - (highVertices q G).card ≤
      (regularNeighbors q G l).card := by
  have hCover : G.neighborFinset l ⊆
      regularNeighbors q G l ∪ lowNeighbors q G l ∪ highVertices q G := by
    intro v hv
    by_cases hZero : signedDeficiency q G v = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hZero⟩))
    · by_cases hLow : 0 < signedDeficiency q G v
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hLow⟩))
      · exact Finset.mem_union_right _ ((mem_highVertices_iff q G v).mpr (by omega))
  have hCard := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hUnion := Finset.card_union_le (regularNeighbors q G l) (lowNeighbors q G l)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hCard
  omega

theorem triangular_neighbor_card_bounds {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) :
    (triangularRegularNeighbors q G l).card ≤ (triangularNeighbors G l).card ∧
      (triangularNeighbors G l).card ≤ (triangularRegularNeighbors q G l).card +
        (lowNeighbors q G l).card + (highVertices q G).card := by
  have hSubset : triangularRegularNeighbors q G l ⊆ triangularNeighbors G l := by
    intro v hv
    obtain ⟨hvR, hvTri⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hvR).1, hvTri⟩
  have hCover : triangularNeighbors G l ⊆
      triangularRegularNeighbors q G l ∪ lowNeighbors q G l ∪ highVertices q G := by
    intro v hv
    obtain ⟨hvN, hvTri⟩ := Finset.mem_filter.mp hv
    by_cases hZero : signedDeficiency q G v = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hvN, hZero⟩, hvTri⟩))
    · by_cases hLow : 0 < signedDeficiency q G v
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvN, hLow⟩))
      · exact Finset.mem_union_right _ ((mem_highVertices_iff q G v).mpr (by omega))
  refine ⟨Finset.card_le_card hSubset, ?_⟩
  have hCard := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hUnion := Finset.card_union_le (triangularRegularNeighbors q G l) (lowNeighbors q G l)
  omega

/-- The triangle-cover estimate controls the error from the triangular proportion. -/
theorem triangular_neighbor_quadratic_bound (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) :
    let k := signedDeficiency q G l
    let δ : ℤ := (lowNeighbors q G l).card
    let h : ℤ := (highVertices q G).card
    let τ : ℤ := (triangularNeighbors G l).card
    (q : ℤ) * τ - τ ^ 2 ≤ (2 * k + 2 * δ + 2 * h) * (q + 2) +
      ∑ v, positiveDeficiency q G v := by
  dsimp only
  let u : ℤ := (triangularRegularNeighbors q G l).card
  let r : ℤ := (regularNeighbors q G l).card
  let τ : ℤ := (triangularNeighbors G l).card
  let δ : ℤ := (lowNeighbors q G l).card
  let h : ℤ := (highVertices q G).card
  let k := signedDeficiency q G l
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hτ := triangular_neighbor_card_bounds q G l
  have huτ : u ≤ τ := by dsimp [u, τ]; exact_mod_cast hτ.1
  have hτu : τ ≤ u + δ + h := by dsimp [τ, u, δ, h]; exact_mod_cast hτ.2
  have huDegree : u ≤ G.degree l := by
    have hSubset : triangularRegularNeighbors q G l ⊆ G.neighborFinset l := by
      intro v hv
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
    dsimp [u]
    exact_mod_cast (show (triangularRegularNeighbors q G l).card ≤ G.degree l by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card hSubset)
  have hD : (G.degree l : ℤ) = (q : ℤ) + 1 - k := by
    dsimp [k]
    unfold signedDeficiency
    ring
  have huq : u ≤ (q : ℤ) + 2 := by
    have hCap : (G.degree l : ℤ) ≤ (q : ℤ) + 2 := by exact_mod_cast hDegree l
    omega
  have hR := regular_neighbor_card_lower q G l
  change (G.degree l : ℤ) - δ - h ≤ r at hR
  have hCover := triangle_cover_bound q G hFree l hLow
  change u * (r - u - 1) ≤ k * G.degree l + ∑ v, positiveDeficiency q G v at hCover
  have hRegularScaled := mul_le_mul_of_nonneg_left hR hu
  have hPositive : 0 ≤ k + δ + h := by dsimp [k]; omega
  have hUScaled := mul_le_mul_of_nonneg_left huq hPositive
  have hKD := mul_le_mul_of_nonneg_left
    (show (G.degree l : ℤ) ≤ (q : ℤ) + 2 by exact_mod_cast hDegree l)
    (show 0 ≤ k by dsimp [k]; omega)
  have hCompareSquare : u ^ 2 ≤ τ ^ 2 := by nlinarith only [hu, huτ]
  have hCompareLinear := mul_le_mul_of_nonneg_left hτu (Nat.cast_nonneg (α := ℤ) q)
  have hExtra := mul_le_mul_of_nonneg_left
    (show (q : ℤ) ≤ (q : ℤ) + 2 by omega) (show 0 ≤ δ + h by omega)
  change (q : ℤ) * τ - τ ^ 2 ≤ (2 * k + 2 * δ + 2 * h) * (q + 2) + _
  rw [hD] at hRegularScaled
  nlinarith only [hCover, hRegularScaled, hUScaled, hKD, hCompareSquare, hCompareLinear, hExtra]

/-- An additive form of the incidence bound avoids division by the block threshold. -/
theorem large_neighbor_blocks_incidence_additive {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P C : Finset (Fin n)) (t e : ℤ)
    (ht : 0 ≤ t)
    (hLarge : ∀ v ∈ C, t ≤ ((G.neighborFinset v ∩ P).card : ℤ))
    (hPositive : 0 < t ^ 2 - (P.card : ℤ))
    (hError : (P.card : ℤ) ^ 2 ≤ (t ^ 2 - P.card) * e) :
    (∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℤ)) ≤ (P.card : ℤ) + e := by
  have hLargeReal (v) (hv : v ∈ C) : (t : ℝ) ≤ ((G.neighborFinset v ∩ P).card : ℝ) := by
    exact_mod_cast hLarge v hv
  have h := large_neighbor_blocks_incidence_bound G hFree P C t (by exact_mod_cast ht) hLargeReal
  have hInt : (t ^ 2 - (P.card : ℤ)) *
      (∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℤ)) ≤ (P.card : ℤ) * t ^ 2 := by
    exact_mod_cast h
  have hCompare : (t ^ 2 - (P.card : ℤ)) *
      (∑ v ∈ C, ((G.neighborFinset v ∩ P).card : ℤ)) ≤
        (t ^ 2 - P.card) * (P.card + e) := by
    nlinarith only [hInt, hError]
  exact (mul_le_mul_iff_of_pos_left hPositive).mp hCompare

def boundedSmallPairBound (q k c δ F τ p d t : ℤ) : ℤ :=
  (q ^ 2 + k) * (k - 1) * (k - 2) + 2 * (k - 1) * (p + (q + 2) * τ) +
    2 * k * q * δ + 2 * (k + 1) * (q * c + (k + 1) * δ + F) +
    (2 * δ ^ 2 + c ^ 2 + 2 * δ * (δ * k + F)) + 2 * t * (k * d + 3 * d + F)

/-- The small-block estimate includes all high centers with their explicit quadratic cost. -/
theorem all_small_positive_block_pair_sum (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l) (A S : Finset (Fin (q ^ 2 + q + 2)))
    (hA : A ⊆ positivePartners q G l) (hNonA : ∀ v ∈ A, 0 ≤ signedDeficiency q G v)
    (t : ℤ) (ht : 0 ≤ t) (hSmall : ∀ v ∈ S, ((G.neighborFinset v ∩ A).card : ℤ) ≤ t) :
    (∑ v ∈ S, (((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card)) ≤
      boundedSmallPairBound q (signedDeficiency q G l)
        (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) (lowNeighbors q G l).card
        (∑ w, positiveDeficiency q G w) (triangularNeighbors G l).card
        (positivePartners q G l).card (G.degree l) t + (highVertices q G).card * t ^ 2 := by
  let U := S \ highVertices q G
  let T := U ∩ nonneighborCenters G l
  let H := S ∩ highVertices q G
  let f := fun v => ((G.neighborFinset v ∩ A).card : ℤ) ^ 2 - (G.neighborFinset v ∩ A).card
  have hTS : T ⊆ S := fun _ hv => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).1).1
  have hCenters : T ⊆ nonneighborCenters G l := Finset.inter_subset_right
  have hNonT (v) (hv : v ∈ T) : 0 ≤ signedDeficiency q G v := by
    have hNot := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).1).2
    have h := (mem_highVertices_iff q G v).not.mp hNot
    omega
  have hSmallT (v) (hv : v ∈ T) : ((G.neighborFinset v ∩ A).card : ℤ) ≤ t := hSmall v (hTS hv)
  have hMain := small_block_pair_sum_explicit q G hFree hDegree l hLow A ∅ T
    (Finset.disjoint_empty_right A) hA (Finset.empty_subset _) hCenters hNonT t ht hSmallT
  simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, sub_zero, add_zero] at hMain
  change (∑ v ∈ T, f v) ≤ boundedSmallPairBound q (signedDeficiency q G l)
    (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) (lowNeighbors q G l).card
    (∑ w, positiveDeficiency q G w) (triangularNeighbors G l).card
    (positivePartners q G l).card (G.degree l) t at hMain
  have hUT : (∑ v ∈ U, f v) = ∑ v ∈ T, f v := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hvU hvNot
    have hNotCenter : v ∉ nonneighborCenters G l := fun h => hvNot (Finset.mem_inter.mpr ⟨hvU, h⟩)
    have hCenter : v = l ∨ G.Adj l v := by
      by_cases hEq : v = l
      · exact Or.inl hEq
      · apply Or.inr
        by_contra hNot
        exact hNotCenter ((nonneighborCenters_mem_iff G l v).mpr ⟨hEq, hNot⟩)
    have hEmpty := nonhigh_positive_block_empty q G l hLow A hA hNonA v hCenter
    simp [f, hEmpty]
  have hHighEach (v) (hv : v ∈ H) : f v ≤ t ^ 2 := by
    have hmt := hSmall v (Finset.mem_inter.mp hv).1
    have hm : (0 : ℤ) ≤ (G.neighborFinset v ∩ A).card := by positivity
    dsimp [f]
    nlinarith only [hmt, hm, ht, mul_nonneg (sub_nonneg.mpr hmt) (show 0 ≤ t + (G.neighborFinset v ∩ A).card by omega)]
  have hHighSum := Finset.sum_le_sum hHighEach
  simp only [Finset.sum_const, nsmul_eq_mul] at hHighSum
  have hHighCard : (H.card : ℤ) ≤ (highVertices q G).card := by
    exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right : H ⊆ highVertices q G))
  have hHighScaled := mul_le_mul_of_nonneg_right hHighCard (sq_nonneg t)
  have hSets : S \ H = U := by
    ext v
    simp only [U, H, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hSplit := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : H ⊆ S)
  rw [hSets, hUT] at hSplit
  change (∑ v ∈ S, f v) ≤ _
  linarith only [hMain, hHighSum, hHighScaled, hSplit]

/-- The finite bounded-deficiency comparison retains the block threshold and incidence error. -/
theorem bounded_graph_comparison (q C : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (l : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G l)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (t e : ℤ) (ht : 0 ≤ t)
    (hThreshold : 0 < t ^ 2 - ((regularPositivePartners q G l).card : ℤ))
    (hError : ((regularPositivePartners q G l).card : ℤ) ^ 2 ≤
      (t ^ 2 - (regularPositivePartners q G l).card) * e) :
    let k := signedDeficiency q G l
    let c := ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w
    let δ : ℤ := (lowNeighbors q G l).card
    let F := ∑ w, positiveDeficiency q G w
    let τ : ℤ := (triangularNeighbors G l).card
    let p : ℤ := (positivePartners q G l).card
    let d : ℤ := G.degree l
    let h : ℤ := (highVertices q G).card
    let m : ℤ := (regularPositivePartners q G l).card
    let L : ℤ := 8 * C
    L * (m * (m - 1)) ≤
      L * (m + t * F + boundedSmallPairBound q k c δ F τ p d t + h * t ^ 2) +
        ((L - 1) * q + L) * (m + e) := by
  let A := regularPositivePartners q G l
  let S := Finset.univ.filter fun v => ((G.neighborFinset v ∩ A).card : ℤ) ≤ t
  let R := Finset.univ \ S
  have hA : A ⊆ positivePartners q G l := Finset.filter_subset _ _
  have hReg (v) (hv : v ∈ A) : signedDeficiency q G v = 0 := (Finset.mem_filter.mp hv).2
  have hNonA (v) (hv : v ∈ A) : 0 ≤ signedDeficiency q G v := le_of_eq (hReg v hv).symm
  have hSmall (v) (hv : v ∈ S) : ((G.neighborFinset v ∩ A).card : ℤ) ≤ t :=
    (Finset.mem_filter.mp hv).2
  have hLarge (v) (hv : v ∈ R) : t ≤ ((G.neighborFinset v ∩ A).card : ℤ) := by
    have hNot := (Finset.mem_sdiff.mp hv).2
    have hNotSmall : ¬ ((G.neighborFinset v ∩ A).card : ℤ) ≤ t := by
      intro h
      exact hNot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have hCoverage := regular_set_remaining_pair_demand q G hFree A S hReg t ht hSmall
  have hSmallSum := all_small_positive_block_pair_sum q G hFree hDegree l hLow A S hA hNonA t ht hSmall
  have hLargeSum := no_cheap_edge_weighted_pair_sum_le q C G hFree hDegree l hLow A R hA hNonA hNoCheap
  have hIncidence := large_neighbor_blocks_incidence_additive G hFree A R t e ht hLarge hThreshold hError
  have hL : (0 : ℤ) ≤ 8 * C := by positivity
  have hQ : (0 : ℤ) ≤ (8 * (C : ℤ) - 1) * q + 8 * C := by
    have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
    exact add_nonneg (mul_nonneg (by omega) (Nat.cast_nonneg q)) (by omega)
  have hCoverageScaled := mul_le_mul_of_nonneg_left hCoverage hL
  have hSmallScaled := mul_le_mul_of_nonneg_left hSmallSum hL
  have hIncidenceScaled := mul_le_mul_of_nonneg_left hIncidence hQ
  dsimp only
  change _ ≤ (8 * (C : ℤ) * ((A.card : ℤ) + t * _ + _ + _)) + _
  change (8 * (C : ℤ)) * _ ≤ (8 * C * ((q : ℤ) + 1) - q) * _ at hLargeSum
  nlinarith only [hCoverageScaled, hSmallScaled, hLargeSum, hIncidenceScaled]

/-- A uniform error bound for the finite small-block polynomial. -/
theorem bounded_small_pair_error_le (q k K c δ F τ p d t : ℤ)
    (hq : 1 ≤ q) (hK : 1 ≤ K) (hk : 1 ≤ k) (hkK : k ≤ K)
    (hc : 0 ≤ c) (hcq : c ≤ q) (hδ : 0 ≤ δ) (hδq : δ ≤ q)
    (hF : 0 ≤ F) (hFq : F ≤ 3 * q) (hτ : 0 ≤ τ) (hτq : τ ≤ 3 * q)
    (hp : 0 ≤ p) (hpq : p ≤ (K + 4) * q)
    (hd : 0 ≤ d) (hdq : d ≤ 3 * q) (ht : 0 ≤ t) :
    boundedSmallPairBound q k c δ F τ p d t -
        (q ^ 2 * (k - 1) * (k - 2) + 2 * (k - 1) * q * τ) ≤
      100 * (K + 1) ^ 3 * q * (1 + c + δ + t) := by
  let J := K + 1
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hkJ : k ≤ J := by dsimp [J]; omega
  have hJ2 : J ≤ J ^ 2 := by nlinarith
  have hJ3 : J ^ 2 ≤ J ^ 3 := by nlinarith [mul_nonneg (show 0 ≤ J by omega) (show 0 ≤ J ^ 2 - J by omega)]
  have hJ30 : 0 ≤ J ^ 3 := by positivity
  have hkCube : k ^ 3 ≤ J ^ 3 := pow_le_pow_left₀ (by omega) hkJ 3
  have hCubic : k * (k - 1) * (k - 2) ≤ J ^ 3 * q := by
    have h1 : k * (k - 1) * (k - 2) ≤ k ^ 3 := by nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ 3 * k - 2 by omega)]
    have h2 := mul_le_mul_of_nonneg_left hq hJ30
    nlinarith only [h1, hkCube, h2]
  have hPτ : p + 2 * τ ≤ 10 * J * q := by
    dsimp [J]
    nlinarith only [hpq, hτq, mul_nonneg (show 0 ≤ K by omega) (show 0 ≤ q by omega)]
  have hReg : 2 * (k - 1) * (p + 2 * τ) ≤ 20 * J ^ 3 * q := by
    have h1 := mul_le_mul (show k - 1 ≤ J by omega) hPτ
      (show 0 ≤ p + 2 * τ by omega) (show 0 ≤ J by omega)
    have h2 := mul_le_mul_of_nonneg_right hJ3 (show 0 ≤ q by omega)
    nlinarith only [h1, h2]
  have hJq : J ≤ J ^ 3 := hJ2.trans hJ3
  have hFterm : 2 * (k + 1) * F ≤ 12 * J ^ 3 * q := by
    have h1 := mul_le_mul (show k + 1 ≤ 2 * J by omega) hFq hF (show 0 ≤ 2 * J by omega)
    have h2 := mul_le_mul_of_nonneg_right hJq (show 0 ≤ q by omega)
    nlinarith only [h1, h2]
  have hCterm : 2 * (k + 1) * q * c + c ^ 2 ≤ 5 * J ^ 3 * q * c := by
    have h1 := mul_le_mul_of_nonneg_right (show k + 1 ≤ 2 * J by omega)
      (show 0 ≤ q * c by positivity)
    have h2 := mul_le_mul_of_nonneg_right hJq (show 0 ≤ q * c by positivity)
    have h3 := mul_le_mul_of_nonneg_right hcq hc
    have h4 := mul_le_mul_of_nonneg_right (show 1 ≤ J ^ 3 by omega) (show 0 ≤ q * c by positivity)
    nlinarith only [h1, h2, h3, h4]
  have hδterm : 2 * k * q * δ + 2 * (k + 1) ^ 2 * δ +
      2 * δ ^ 2 + 2 * δ * (δ * k + F) ≤ 30 * J ^ 3 * q * δ := by
    have h1 := mul_le_mul_of_nonneg_right hkJ (show 0 ≤ q * δ by positivity)
    have h2sq : (k + 1) ^ 2 ≤ 4 * J ^ 2 := by
      have h := sq_le_sq₀ (show 0 ≤ k + 1 by omega) (show 0 ≤ 2 * J by omega)
      have h2 := h.mpr (show k + 1 ≤ 2 * J by omega)
      nlinarith only [h2]
    have h2 := mul_le_mul_of_nonneg_right h2sq hδ
    have h2b := mul_le_mul_of_nonneg_right hq (show 0 ≤ J ^ 2 * δ by positivity)
    have h3 := mul_le_mul_of_nonneg_right hδq hδ
    have h4 := mul_le_mul hδq hkJ (show 0 ≤ k by omega) (show 0 ≤ q by omega)
    have h4b := mul_le_mul_of_nonneg_left (add_le_add h4 hFq) hδ
    have h5 := mul_le_mul_of_nonneg_right hJq (show 0 ≤ q * δ by positivity)
    have h6 := mul_le_mul_of_nonneg_right hJ3 (show 0 ≤ q * δ by positivity)
    have h7 := mul_le_mul_of_nonneg_right (show 1 ≤ J ^ 3 by omega) (show 0 ≤ q * δ by positivity)
    nlinarith only [h1, h2, h2b, h3, h4b, h5, h6, h7,
      mul_nonneg hJ30 (show 0 ≤ q * δ by positivity)]
  have hTterm : 2 * t * (k * d + 3 * d + F) ≤ 30 * J ^ 3 * q * t := by
    have h1 := mul_le_mul hkJ hdq hd (show 0 ≤ J by omega)
    have h2 : k * d + 3 * d + F ≤ 15 * J * q := by
      nlinarith only [h1, hdq, hFq, mul_nonneg (show 0 ≤ J - 1 by omega) (show 0 ≤ q by omega)]
    have h3 := mul_le_mul_of_nonneg_left h2 ht
    have h4 := mul_le_mul_of_nonneg_right hJq (show 0 ≤ q * t by positivity)
    nlinarith only [h3, h4]
  have hSpare : 0 ≤ J ^ 3 * q * (67 + 95 * c + 70 * δ + 70 * t) := by positivity
  unfold boundedSmallPairBound
  change _ ≤ 100 * J ^ 3 * q * (1 + c + δ + t)
  nlinarith only [hCubic, hReg, hFterm, hCterm, hδterm, hTterm, hSpare]

/-- Under the block comparison, an active bounded-deficiency row has a quantitative local obstruction. -/
theorem bounded_local_numeric_obstruction (q k K c b δ F τ p d h m t e L : ℤ)
    (hq : 1 ≤ q) (hK : 1 ≤ K) (hk : 1 ≤ k) (hkK : k ≤ K) (hKq : K ≤ q)
    (hc : 0 ≤ c) (hcq : c ≤ q) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hδq : δ ≤ q)
    (hF : 0 ≤ F) (hFq : F ≤ 3 * q) (hτ : 0 ≤ τ) (hτq : τ ≤ 3 * q)
    (hp : 0 ≤ p) (hpq : p ≤ (K + 4) * q)
    (hd : 0 ≤ d) (hdq : d ≤ 3 * q) (hh : 0 ≤ h)
    (ht : 0 ≤ t) (htq : t ≤ q) (he : 0 ≤ e) (hL : 1 ≤ L)
    (hRowsLower : (k - 1) * q + τ - b - 2 * h ≤ m)
    (hRowsUpper : m ≤ (k - 1) * q + τ + k + c)
    (hTriangle : q * τ - τ ^ 2 ≤ (2 * k + 2 * δ + 2 * h) * (q + 2) + F)
    (hActive : 2 ≤ k ∨ q ≤ 2 * τ)
    (hComparison : L * (m * (m - 1)) ≤
      L * (m + t * F + boundedSmallPairBound q k c δ F τ p d t + h * t ^ 2) +
        ((L - 1) * q + L) * (m + e)) :
    q ≤ 400 * L * (K + h + 3) ^ 3 * (1 + b + c + δ + t + e) := by
  let A := (k - 1) * q + τ
  let Q := (L - 1) * q + L
  let R := K + h + 3
  let w := 1 + b + c + δ + t + e
  let Z := R ^ 3 * q * w
  have hq0 : 0 ≤ q := by omega
  have hL0 : 0 ≤ L := by omega
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (mul_nonneg (by omega) hq0) hτ
  have hR : 4 ≤ R := by dsimp [R]; omega
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hR2 : R ≤ R ^ 2 := by nlinarith only [hR]
  have hR3 : R ^ 2 ≤ R ^ 3 := by
    nlinarith only [mul_nonneg (show 0 ≤ R by omega) (show 0 ≤ R ^ 2 - R by omega)]
  have hRCube : R ≤ R ^ 3 := hR2.trans hR3
  have hR0 : 0 ≤ R := by omega
  have hw0 : 0 ≤ w := by omega
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hRwR : R ≤ R * w := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw hR0
  have hRww : w ≤ R * w := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1 ≤ R by omega) hw0
  have hRqW : R * q * w ≤ Z := by
    dsimp [Z]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRCube hq0) hw0
  have hR2qW : R ^ 2 * q * w ≤ Z := by
    dsimp [Z]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR3 hq0) hw0
  have hqw : q * w ≤ Z := by
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ R ^ 3 by omega) (mul_nonneg hq0 hw0)
    dsimp [Z]
    nlinarith only [h]
  have hRq : R * q ≤ Z := by
    have h := mul_le_mul_of_nonneg_left hw (mul_nonneg hR0 hq0)
    nlinarith only [h, hRqW]
  have hABound : A ≤ R * q := by
    dsimp [A, R]
    have h1 := mul_le_mul_of_nonneg_right hkK hq0
    have h2 := mul_nonneg hh hq0
    nlinarith only [h1, h2, hτq, hq0]
  have hmBound : m ≤ 2 * R * q := by
    change m ≤ A + k + c at hRowsUpper
    have hRQ := mul_nonneg (show 0 ≤ R - 2 by omega) hq0
    nlinarith only [hRowsUpper, hABound, hkK, hKq, hcq, hRQ]
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg (mul_nonneg (by omega) hq0) hL0
  have hQBound : Q ≤ 2 * L * q := by
    dsimp [Q]
    nlinarith only [mul_nonneg hL0 (show 0 ≤ q - 1 by omega), hq0]
  have hSmall := bounded_small_pair_error_le q k K c δ F τ p d t hq hK hk hkK
    hc hcq hδ hδq hF hFq hτ hτq hp hpq hd hdq ht
  have hKCubed : (K + 1) ^ 3 ≤ R ^ 3 := by
    apply pow_le_pow_left₀ (by omega)
    dsimp [R]
    omega
  have hSmallFactor : (K + 1) ^ 3 * q * (1 + c + δ + t) ≤ Z := by
    dsimp [Z, w]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hKCubed hq0
    · omega
    · positivity
    · positivity
  have hSmallBound : boundedSmallPairBound q k c δ F τ p d t -
      (q ^ 2 * (k - 1) * (k - 2) + 2 * (k - 1) * q * τ) ≤ 100 * Z := by
    nlinarith only [hSmall, hSmallFactor]
  have hRowsScaled := mul_le_mul_of_nonneg_left hRowsLower hA0
  have hSquared : A ^ 2 - 2 * A * (b + 2 * h) ≤ m ^ 2 := by
    change A - b - 2 * h ≤ m at hRowsLower
    change A * ((k - 1) * q + τ - b - 2 * h) ≤ A * m at hRowsScaled
    change A * (A - b - 2 * h) ≤ A * m at hRowsScaled
    nlinarith only [hRowsScaled, sq_nonneg (m - A)]
  have hSquaredScaled := mul_le_mul_of_nonneg_left hSquared hL0
  have hRowQ := mul_le_mul_of_nonneg_left hRowsUpper hQ0
  have hSmallScaled := mul_le_mul_of_nonneg_left hSmallBound hL0
  have hTriangleScaled := mul_le_mul_of_nonneg_left hTriangle hL0
  have hMain : q * A ≤ 2 * L * A * (b + 2 * h) + L * (2 * m + A) + 100 * L * Z +
      L * t * F + L * h * t ^ 2 + Q * (k + c + e) +
      L * ((2 * k + 2 * δ + 2 * h) * (q + 2) + F) := by
    dsimp only [A, Q] at hSquaredScaled hRowQ ⊢
    linear_combination hComparison + hSquaredScaled + hRowQ + hSmallScaled + hTriangleScaled
  have hBW : b + 2 * h ≤ 3 * R * w := by
    have hbW : b ≤ w := by dsimp [w]; omega
    have hhR : h ≤ R := by dsimp [R]; omega
    nlinarith only [hbW, hhR, hRwR, hRww]
  have hATerm : 2 * A * (b + 2 * h) ≤ 6 * Z := by
    have h := mul_le_mul hABound hBW (show 0 ≤ b + 2 * h by omega) (mul_nonneg hR0 hq0)
    nlinarith only [h, hR2qW]
  have hMTerm : 2 * m + A ≤ 5 * Z := by nlinarith only [hmBound, hABound, hRq]
  have hFTerm : t * F ≤ 3 * Z := by
    have h1 := mul_le_mul_of_nonneg_left hFq ht
    have h2 := mul_le_mul_of_nonneg_left (show t ≤ w by dsimp [w]; omega) hq0
    nlinarith only [h1, h2, hqw]
  have hHTerm : h * t ^ 2 ≤ Z := by
    have h1 := mul_le_mul_of_nonneg_left htq ht
    have h2 := mul_le_mul_of_nonneg_left h1 hh
    have h3 := mul_le_mul (show h ≤ R by dsimp [R]; omega)
      (show t ≤ w by dsimp [w]; omega) ht hR0
    have h4 := mul_le_mul_of_nonneg_right h3 hq0
    nlinarith only [h2, h4, hRqW]
  have hKCE : k + c + e ≤ 2 * R * w := by
    have h1 : k ≤ R := by dsimp [R]; omega
    have h2 : c + e ≤ w := by dsimp [w]; omega
    nlinarith only [h1, h2, hRwR, hRww]
  have hQTerm : Q * (k + c + e) ≤ 4 * L * Z := by
    have h1 := mul_le_mul hQBound hKCE (show 0 ≤ k + c + e by omega) (show 0 ≤ 2 * L * q by positivity)
    have h2 := mul_le_mul_of_nonneg_left hRqW hL0
    nlinarith only [h1, h2]
  have hTriangleTerm : (2 * k + 2 * δ + 2 * h) * (q + 2) + F ≤ 15 * Z := by
    have h1 : 2 * k + 2 * δ + 2 * h ≤ 4 * R * w := by
      have h2 : k + h ≤ R := by dsimp [R]; omega
      have h3 : δ ≤ w := by dsimp [w]; omega
      nlinarith only [h2, h3, hRwR, hRww]
    have h2 := mul_le_mul h1 (show q + 2 ≤ 3 * q by omega)
      (show 0 ≤ q + 2 by omega) (show 0 ≤ 4 * R * w by positivity)
    have h3 : F ≤ 3 * Z := by
      have h4 := mul_le_mul_of_nonneg_left hw hq0
      nlinarith only [hFq, h4, hqw]
    nlinarith only [h2, hRqW, h3]
  have hAScaled := mul_le_mul_of_nonneg_left hATerm hL0
  have hMScaled := mul_le_mul_of_nonneg_left hMTerm hL0
  have hFScaled := mul_le_mul_of_nonneg_left hFTerm hL0
  have hHScaled := mul_le_mul_of_nonneg_left hHTerm hL0
  have hTriScaled := mul_le_mul_of_nonneg_left hTriangleTerm hL0
  have hUpper : q * A ≤ 200 * L * Z := by
    linear_combination hMain + hAScaled + hMScaled + hFScaled + hHScaled + hQTerm +
      hTriScaled + 66 * (mul_nonneg hL0 hZ)
  have hActiveA : q ≤ 2 * A := by
    dsimp [A]
    rcases hActive with hActive | hActive
    · nlinarith only [hτ, hq0, mul_nonneg (show 0 ≤ k - 2 by omega) hq0]
    · nlinarith only [hActive, mul_nonneg (show 0 ≤ k - 1 by omega) hq0]
  have hActiveScaled := mul_le_mul_of_nonneg_left hActiveA hq0
  have hFinal : q * q ≤ q * (400 * L * R ^ 3 * w) := by
    dsimp [Z] at hUpper
    linear_combination 2 * hUpper + hActiveScaled
  exact (mul_le_mul_iff_of_pos_left (show 0 < q by omega)).mp hFinal

/-- Integer division supplies a small threshold with a controlled incidence error. -/
theorem block_threshold_parameters (q M T m : ℤ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hm : 0 ≤ m) (hmq : m ≤ M * q) (hLarge : 16 * M ^ 2 * T ^ 3 ≤ q) :
    let t := q / T
    0 ≤ t ∧ t ≤ q ∧ T * t ≤ q ∧ 0 < t ^ 2 - m ∧ m ^ 2 ≤ (t ^ 2 - m) * t := by
  let t := q / T
  have hM0 : 0 ≤ M := by omega
  have hT0 : 0 ≤ T := by omega
  have hM2 : 1 ≤ M ^ 2 := by nlinarith only [hM]
  have hT2 : 1 ≤ T ^ 2 := by nlinarith only [hT]
  have hT3 : T ≤ T ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hT2 hT0
    nlinarith only [h]
  have hT3nonneg : 0 ≤ T ^ 3 := by positivity
  have hMT3 : T ≤ M ^ 2 * T ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hM2 hT3nonneg
    nlinarith only [h, hT3]
  have hqT : 2 * T ≤ q := by nlinarith only [hLarge, hMT3, hT]
  have hq : 1 ≤ q := by omega
  have hq0 : 0 ≤ q := by omega
  have ht : 0 ≤ t := Int.ediv_nonneg hq0 hT0
  have hTt : T * t ≤ q := Int.mul_ediv_self_le (by omega)
  have hFloor : q < T * t + T := Int.lt_mul_ediv_self_add (by omega)
  have hLower : q ≤ 2 * T * t := by nlinarith only [hFloor, hqT]
  have htq : t ≤ q := by nlinarith only [hTt, mul_nonneg (show 0 ≤ T - 1 by omega) ht]
  have htPos : 0 < t := by
    by_contra h
    have htZero : t = 0 := by omega
    rw [htZero] at hLower
    omega
  have hCube := pow_le_pow_left₀ hq0 hLower 3
  have hLargeScaled := mul_le_mul_of_nonneg_right hLarge (sq_nonneg q)
  have hScaled : (8 * T ^ 3) * (2 * M ^ 2 * q ^ 2) ≤ (8 * T ^ 3) * t ^ 3 := by
    nlinarith only [hCube, hLargeScaled]
  have hCubeLower : 2 * M ^ 2 * q ^ 2 ≤ t ^ 3 :=
    (mul_le_mul_iff_of_pos_left (show 0 < 8 * T ^ 3 by positivity)).mp hScaled
  have hM1 : 1 ≤ M * q := by
    nlinarith only [hM, hq, mul_nonneg (show 0 ≤ M - 1 by omega) (show 0 ≤ q - 1 by omega)]
  have hM2q2 : 1 ≤ M ^ 2 * q ^ 2 := by nlinarith only [hM1]
  have hSquare := pow_le_pow_left₀ hm hmq 2
  have hmt : m * t ≤ M ^ 2 * q ^ 2 := by
    have h1 := mul_le_mul hmq htq ht (mul_nonneg hM0 hq0)
    have h2 := mul_le_mul_of_nonneg_right (show M ≤ M ^ 2 by nlinarith only [hM]) (sq_nonneg q)
    nlinarith only [h1, h2]
  have hPositiveProduct : 0 < t * (t ^ 2 - m) := by nlinarith only [hCubeLower, hmt, hM2q2]
  have hPositive : 0 < t ^ 2 - m := (mul_pos_iff_of_pos_left htPos).mp hPositiveProduct
  refine ⟨ht, htq, hTt, hPositive, ?_⟩
  nlinarith only [hSquare, hmt, hCubeLower]

/-- Active rows with bounded deficiency obey a finite, uniform local obstruction. -/
theorem bounded_deficiency_local_obstruction (q C K : ℕ) (hC : 1 ≤ C)
    (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (hBound : signedDeficiency q G l ≤ K)
    (hNeighborWeight : (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) ≤ q)
    (hActive : 2 ≤ signedDeficiency q G l ∨ (q : ℤ) ≤ 2 * (triangularRegularNeighbors q G l).card)
    (t e : ℤ) (ht : 0 ≤ t) (htq : t ≤ q) (he : 0 ≤ e)
    (hThreshold : 0 < t ^ 2 - ((regularPositivePartners q G l).card : ℤ))
    (hError : ((regularPositivePartners q G l).card : ℤ) ^ 2 ≤
      (t ^ 2 - (regularPositivePartners q G l).card) * e) :
    (q : ℤ) ≤ 400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3 *
      (1 + (lowPositivePartners q G l).card +
        (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) +
        (lowNeighbors q G l).card + t + e) := by
  let k := signedDeficiency q G l
  let c := ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w
  let b : ℤ := (lowPositivePartners q G l).card
  let δ : ℤ := (lowNeighbors q G l).card
  let F := ∑ w, positiveDeficiency q G w
  let τ : ℤ := (triangularNeighbors G l).card
  let p : ℤ := (positivePartners q G l).card
  let d : ℤ := G.degree l
  let h : ℤ := (highVertices q G).card
  let m : ℤ := (regularPositivePartners q G l).card
  let L : ℤ := 8 * C
  have hq : (1 : ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hKInt : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hKqInt : (K : ℤ) ≤ q := by exact_mod_cast hKq
  have hk : 1 ≤ k := hLow
  have hkK : k ≤ K := hBound
  have hc : 0 ≤ c := Finset.sum_nonneg (fun w _ => positiveDeficiency_nonnegative q G w)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hF : 0 ≤ F := Finset.sum_nonneg (fun w _ => positiveDeficiency_nonnegative q G w)
  have hFBound := dense_positiveDeficiency_le_high_card q G hDegree hDense
  have hHighInt : h ≤ q := by dsimp [h]; exact_mod_cast hHigh
  have hFq : F ≤ 3 * (q : ℤ) := by change F ≤ 2 * (q : ℤ) + h - 4 at hFBound; omega
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hDegreeEq : d = (q : ℤ) + 1 - k := by
    dsimp [d, k]
    unfold signedDeficiency
    ring
  have hdq : d ≤ 3 * (q : ℤ) := by omega
  have hδDegree : δ ≤ d := by
    dsimp [δ, d]
    exact_mod_cast (show (lowNeighbors q G l).card ≤ G.degree l by
      simpa only [lowNeighbors, SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (Finset.filter_subset (fun w => 0 < signedDeficiency q G w) (G.neighborFinset l)))
  have hδq : δ ≤ q := by omega
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτDegree : τ ≤ d := by
    dsimp [τ, d]
    exact_mod_cast (show (triangularNeighbors G l).card ≤ G.degree l by
      simpa only [triangularNeighbors, SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (Finset.filter_subset (fun w => codegree G l w = 1) (G.neighborFinset l)))
  have hτq : τ ≤ 3 * (q : ℤ) := by omega
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hPBound := low_positivePartners_card_upper q G hFree l hLow
  rw [triangle_codegree_sum_eq_card G hFree l] at hPBound
  have hPUpper : p ≤ (k - 1) * q + k + c + τ := by
    exact hPBound
  have hpq : p ≤ ((K : ℤ) + 4) * q := by
    have hScale := mul_le_mul_of_nonneg_right hkK (Nat.cast_nonneg (α := ℤ) q)
    change c ≤ q at hNeighborWeight
    nlinarith only [hPUpper, hScale, hkK, hKqInt, hNeighborWeight, hτDegree, hDegreeEq, hk, hq]
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hRows := regular_positivePartners_card_bounds q G hFree hDegree l hLow
  change (k - 1) * q + k + c + τ - b - 2 * h ≤ m ∧
    m ≤ (k - 1) * q + k + c + τ - b at hRows
  have hRowsLower : (k - 1) * q + τ - b - 2 * h ≤ m := by omega
  have hRowsUpper : m ≤ (k - 1) * q + τ + k + c := by omega
  have hTriangle := triangular_neighbor_quadratic_bound q G hFree hDegree l hLow
  change (q : ℤ) * τ - τ ^ 2 ≤ (2 * k + 2 * δ + 2 * h) * (q + 2) + F at hTriangle
  have hTriRegular : ((triangularRegularNeighbors q G l).card : ℤ) ≤ τ := by
    dsimp [τ]
    exact_mod_cast (triangular_neighbor_card_bounds q G l).1
  have hActiveInt : 2 ≤ k ∨ (q : ℤ) ≤ 2 * τ := by rcases hActive with hActive | hActive <;> omega
  have hCompare := bounded_graph_comparison q C hC G hFree hDegree l hLow hNoCheap t e ht hThreshold hError
  change L * (m * (m - 1)) ≤
    L * (m + t * F + boundedSmallPairBound q k c δ F τ p d t + h * t ^ 2) +
      ((L - 1) * q + L) * (m + e) at hCompare
  exact bounded_local_numeric_obstruction q k K c b δ F τ p d h m t e L hq hKInt hk hkK hKqInt
    hc hNeighborWeight hb hδ hδq hF hFq hτ hτq hp hpq hd hdq hh ht htq he hL
    hRowsLower hRowsUpper hTriangle hActiveInt hCompare

/-- An active bounded-deficiency vertex with small neighboring deficiency has many low positive partners. -/
theorem bounded_deficiency_many_low_partners (q C K : ℕ) (hC : 1 ≤ C)
    (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (hBound : signedDeficiency q G l ≤ K)
    (hNeighborWeight : (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) ≤ q)
    (hActive : 2 ≤ signedDeficiency q G l ∨ (q : ℤ) ≤ 2 * (triangularRegularNeighbors q G l).card)
    (hSparse :
      8 * (400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3) *
        (1 + (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) + (lowNeighbors q G l).card) ≤ q)
    (hSize :
      16 * ((K : ℤ) + 4) ^ 2 *
        (16 * (400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3)) ^ 3 ≤ q) :
    (q : ℤ) ≤ 2 * (400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3) *
      (lowPositivePartners q G l).card := by
  let k := signedDeficiency q G l
  let c := ∑ w ∈ G.neighborFinset l, positiveDeficiency q G w
  let δ : ℤ := (lowNeighbors q G l).card
  let b : ℤ := (lowPositivePartners q G l).card
  let m : ℤ := (regularPositivePartners q G l).card
  let h : ℤ := (highVertices q G).card
  let D := 400 * (8 * (C : ℤ)) * ((K : ℤ) + h + 3) ^ 3
  let T := 16 * D
  let t := (q : ℤ) / T
  have hq : (1 : ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hKInt : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hKqInt : (K : ℤ) ≤ q := by exact_mod_cast hKq
  have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hDPos : 0 < D := by dsimp [D]; positivity
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hRows := regular_positivePartners_card_bounds q G hFree hDegree l hLow
  have hτDegree : ((triangularNeighbors G l).card : ℤ) ≤ G.degree l := by
    exact_mod_cast (show (triangularNeighbors G l).card ≤ G.degree l by
      simpa only [triangularNeighbors, SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (Finset.filter_subset (fun w => codegree G l w = 1) (G.neighborFinset l)))
  have hDegreeEq : (G.degree l : ℤ) = (q : ℤ) + 1 - k := by
    dsimp [k]
    unfold signedDeficiency
    ring
  have hMUpper : m ≤ ((K : ℤ) + 4) * q := by
    have hRowUpper := hRows.2
    change m ≤ (k - 1) * q + k + c + (triangularNeighbors G l).card - b at hRowUpper
    have hB : 0 ≤ b := by dsimp [b]; positivity
    have hScale := mul_le_mul_of_nonneg_right hBound (Nat.cast_nonneg (α := ℤ) q)
    change c ≤ q at hNeighborWeight
    have hk : 1 ≤ k := hLow
    have hkK : k ≤ K := hBound
    nlinarith only [hRowUpper, hτDegree, hDegreeEq, hB, hScale, hNeighborWeight, hk, hkK, hKqInt, hq]
  have hLarge : 16 * ((K : ℤ) + 4) ^ 2 * T ^ 3 ≤ q := hSize
  obtain ⟨ht, htq, hTt, hThreshold, hError⟩ :=
    block_threshold_parameters q ((K : ℤ) + 4) T m (by omega) hT hm hMUpper hLarge
  have hObstruction := bounded_deficiency_local_obstruction q C K hC hK hKq G hFree hDegree
    hDense hHigh hNoCheap l hLow hBound hNeighborWeight hActive t t ht htq ht hThreshold hError
  change (q : ℤ) ≤ D * (1 + b + c + δ + t + t) at hObstruction
  change 8 * D * (1 + c + δ) ≤ (q : ℤ) at hSparse
  change 16 * D * t ≤ (q : ℤ) at hTt
  change (q : ℤ) ≤ 2 * D * b
  nlinarith only [hObstruction, hSparse, hTt, hq]

/-- Count the incidences of a finite family by its rows or its columns. -/
theorem finite_family_incidence_eq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ) (N : ι → Finset κ) (hN : ∀ w ∈ S, N w ⊆ T) :
    (∑ v ∈ T, ((S.filter fun w => v ∈ N w).card : ℤ)) =
      ∑ w ∈ S, ((N w).card : ℤ) := by
  have hCount (v : κ) : ((S.filter fun w => v ∈ N w).card : ℤ) =
      ∑ w ∈ S, if v ∈ N w then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [hCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.sum_filter]
  have hSet : (T.filter fun v => v ∈ N w) = N w := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hN w hw h, h⟩⟩
  simp [hSet]

/-- Large subsets with small pairwise intersections form a bounded family. -/
theorem finite_family_card_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ) (N : ι → Finset κ) (q B E : ℤ)
    (hq : 0 < q) (hB : 1 ≤ B) (hE : 0 ≤ E)
    (hN : ∀ w ∈ S, N w ⊆ T) (hSize : (T.card : ℤ) ≤ 3 * q)
    (hLarge : ∀ w ∈ S, q ≤ B * (N w).card)
    (hOverlap : ∀ w ∈ S, ∀ u ∈ S, w ≠ u → ((N w ∩ N u).card : ℤ) ≤ E)
    (hSmallOverlap : 6 * B ^ 2 * E ≤ q) : (S.card : ℤ) ≤ 18 * B ^ 2 := by
  let r : ℤ := S.card
  let s : ℤ := T.card
  let a := fun v => ((S.filter fun w => v ∈ N w).card : ℤ)
  let I := ∑ v ∈ T, a v
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hI : 0 ≤ I := Finset.sum_nonneg (fun v _ => by dsimp [a]; positivity)
  have hInc := finite_family_incidence_eq S T N hN
  change I = ∑ w ∈ S, ((N w).card : ℤ) at hInc
  have hILower : r * q ≤ B * I := by
    have h := Finset.sum_le_sum hLarge
    simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← hInc] using h
  have hIUpper : I ≤ r * s := by
    rw [hInc]
    calc
      _ ≤ ∑ _w ∈ S, s := by
        apply Finset.sum_le_sum
        intro w hw
        dsimp [s]
        exact_mod_cast Finset.card_le_card (hN w hw)
      _ = _ := by simp [r]
  have hMoment := incidence_factorial_moment S T N
  have hRowBound (w) (hw : w ∈ S) :
      (∑ u ∈ S.erase w, ((T ∩ N w ∩ N u).card : ℤ)) ≤ r * E := by
    calc
      _ ≤ ∑ _u ∈ S.erase w, E := by
        apply Finset.sum_le_sum
        intro u hu
        have hPair := hOverlap w hw u (Finset.mem_erase.mp hu).2 (Ne.symm (Finset.mem_erase.mp hu).1)
        have hSubset : T ∩ N w ∩ N u ⊆ N w ∩ N u := by
          intro v hv
          exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).2, (Finset.mem_inter.mp hv).2⟩
        have hCard : ((T ∩ N w ∩ N u).card : ℤ) ≤ (N w ∩ N u).card := by
          exact_mod_cast Finset.card_le_card hSubset
        exact hCard.trans hPair
      _ ≤ ∑ _u ∈ S, E := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro _ _ _
        exact hE
      _ = _ := by simp [r]
  have hMomentBound : (∑ v ∈ T, (a v ^ 2 - a v)) ≤ r ^ 2 * E := by
    rw [hMoment]
    have h := Finset.sum_le_sum hRowBound
    simpa only [Finset.sum_const, nsmul_eq_mul, r, pow_two, mul_assoc] using h
  have hSquares : (∑ v ∈ T, a v ^ 2) ≤ I + r ^ 2 * E := by
    rw [Finset.sum_sub_distrib] at hMomentBound
    linarith only [hMomentBound]
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℤ)) a
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCauchy
  change I ^ 2 ≤ s * (∑ v ∈ T, a v ^ 2) at hCauchy
  have hCauchyBound := hCauchy.trans (mul_le_mul_of_nonneg_left hSquares hs)
  have hIUpperScaled := mul_le_mul_of_nonneg_left hIUpper hs
  have hLowerSq := (sq_le_sq₀ (mul_nonneg hr hq.le)
    (mul_nonneg (show 0 ≤ B by omega) hI)).mpr hILower
  have hCauchyScaled := mul_le_mul_of_nonneg_left hCauchyBound (sq_nonneg B)
  have hIUpperScaledB := mul_le_mul_of_nonneg_left hIUpperScaled (sq_nonneg B)
  have hsSq : s ^ 2 ≤ 9 * q ^ 2 := by
    have h := pow_le_pow_left₀ hs hSize 2
    change s ≤ 3 * q at hSize
    nlinarith only [h]
  have hMainTerm := mul_le_mul_of_nonneg_left hsSq (mul_nonneg (sq_nonneg B) hr)
  have hError1 := mul_le_mul_of_nonneg_right hSize (show 0 ≤ 2 * B ^ 2 * E by positivity)
  have hError2 := mul_le_mul_of_nonneg_right hSmallOverlap hq.le
  have hError : 2 * B ^ 2 * s * E ≤ q ^ 2 := by
    change s ≤ 3 * q at hSize
    nlinarith only [hError1, hError2]
  have hErrorScaled := mul_le_mul_of_nonneg_right hError (sq_nonneg r)
  have hFinalScaled : q ^ 2 * r ^ 2 ≤ q ^ 2 * (18 * B ^ 2 * r) := by
    nlinarith only [hLowerSq, hCauchyScaled, hIUpperScaledB, hMainTerm, hErrorScaled]
  have hFinal : r ^ 2 ≤ 18 * B ^ 2 * r :=
    (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hq)).mp hFinalScaled
  by_cases hZero : r = 0
  · change r ≤ _
    rw [hZero]
    positivity
  · have hPos : 0 < r := lt_of_le_of_ne hr (Ne.symm hZero)
    change r ≤ _
    apply (mul_le_mul_iff_of_pos_right hPos).mp
    simpa only [pow_two] using hFinal

def lowVertices {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => 0 < signedDeficiency q G v

def lowHubs {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (lowVertices q G).filter fun v => (q : ℤ) ≤ T * ((lowNeighbors q G v).card : ℤ)

def lowHubClosure {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  lowHubs q T G ∪ (lowVertices q G ∩ (lowHubs q T G).biUnion (fun v => G.neighborFinset v))

theorem lowNeighbors_eq_inter {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    lowNeighbors q G v = G.neighborFinset v ∩ lowVertices q G := by
  ext w
  simp [lowNeighbors, lowVertices]

theorem lowVertices_card_le_positiveDeficiency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    ((lowVertices q G).card : ℤ) ≤ ∑ v, positiveDeficiency q G v := by
  calc
    _ = ∑ _v ∈ lowVertices q G, (1 : ℤ) := by simp
    _ ≤ ∑ v ∈ lowVertices q G, positiveDeficiency q G v := by
      apply Finset.sum_le_sum
      intro v hv
      have h := (Finset.mem_filter.mp hv).2
      unfold positiveDeficiency
      omega
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v _ _
      exact positiveDeficiency_nonnegative q G v

/-- A linear-size low set has only boundedly many vertices with a linear low degree. -/
theorem lowHubs_card_le (q T : ℕ) (hT : 1 ≤ T) (hq : 6 * T ^ 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hSize : ((lowVertices q G).card : ℤ) ≤ 3 * q) :
    ((lowHubs q T G).card : ℤ) ≤ 18 * (T : ℤ) ^ 2 := by
  apply finite_family_card_le (lowHubs q T G) (lowVertices q G)
    (fun v => lowNeighbors q G v) q T 1
  · exact_mod_cast (show 0 < q by nlinarith)
  · exact_mod_cast hT
  · norm_num
  · intro v _
    rw [lowNeighbors_eq_inter]
    exact Finset.inter_subset_right
  · exact hSize
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v _ w _ hvw
    have hSubset : lowNeighbors q G v ∩ lowNeighbors q G w ⊆
        G.neighborFinset v ∩ G.neighborFinset w := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).1,
        (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).1⟩
    have hCount : ((G.neighborFinset v ∩ G.neighborFinset w).card : ℤ) ≤ 1 := by
      exact_mod_cast codegree_le_one G hFree v w hvw
    have hCard : ((lowNeighbors q G v ∩ lowNeighbors q G w).card : ℤ) ≤
        (G.neighborFinset v ∩ G.neighborFinset w).card := by exact_mod_cast Finset.card_le_card hSubset
    exact hCard.trans hCount
  · simpa only [mul_one] using (show 6 * (T : ℤ) ^ 2 ≤ q by exact_mod_cast hq)

theorem dense_lowVertices_card_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q) : ((lowVertices q G).card : ℤ) ≤ 3 * q := by
  have hLow := lowVertices_card_le_positiveDeficiency q G
  have hF := dense_positiveDeficiency_le_high_card q G hDegree hDense
  have hHighInt : ((highVertices q G).card : ℤ) ≤ q := by exact_mod_cast hHigh
  omega

/-- Away from a set of centers, its neighborhood closure has bounded local degree. -/
theorem neighbor_closure_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (S U : Finset (Fin n)) (v : Fin n) (hv : v ∉ U) :
    (G.neighborFinset v ∩ (U ∪ (S ∩ U.biUnion (fun u => G.neighborFinset u)))).card ≤ 2 * U.card := by
  let C := U.biUnion (fun u => G.neighborFinset v ∩ G.neighborFinset u)
  have hCover : G.neighborFinset v ∩ (U ∪ (S ∩ U.biUnion (fun u => G.neighborFinset u))) ⊆
      (G.neighborFinset v ∩ U) ∪ C := by
    intro x hx
    obtain ⟨hxV, hxRest⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hxRest with hxU | hxClosure
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxV, hxU⟩)
    · obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hxClosure).2
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_inter.mpr ⟨hxV, hxu⟩⟩)
  have hEach (u) (hu : u ∈ U) : (G.neighborFinset v ∩ G.neighborFinset u).card ≤ 1 := by
    have hNe : v ≠ u := fun h => hv (h ▸ hu)
    exact codegree_le_one G hFree v u hNe
  have hC : C.card ≤ U.card := by
    calc
      _ ≤ ∑ u ∈ U, (G.neighborFinset v ∩ G.neighborFinset u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ U, 1 := Finset.sum_le_sum hEach
      _ = _ := by simp
  have hUnion := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hFirst : (G.neighborFinset v ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
  omega

theorem lowHubClosure_neighbor_card_le {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) (hv : v ∉ lowHubs q T G) :
    (G.neighborFinset v ∩ lowHubClosure q T G).card ≤ 2 * (lowHubs q T G).card :=
  neighbor_closure_card_le G hFree (lowVertices q G) (lowHubs q T G) v hv

/-- A local large-deficiency estimate bounds every deficiency outside the hub set. -/
theorem deficiency_le_off_lowHubs {n : ℕ} (q T : ℕ) (K : ℤ) (hK : 0 ≤ K)
    (G : SimpleGraph (Fin n))
    (hLocal : ∀ v, K < signedDeficiency q G v → (q : ℤ) ≤ T * ((lowNeighbors q G v).card : ℤ))
    (v : Fin n) (hv : v ∉ lowHubs q T G) : signedDeficiency q G v ≤ K := by
  by_contra h
  have hLarge : K < signedDeficiency q G v := by omega
  have hLow : v ∈ lowVertices q G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  exact hv (Finset.mem_filter.mpr ⟨hLow, hLocal v hLarge⟩)

theorem growing_deficiency_le_off_lowHubs (q C T K : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hq : 32 * C ≤ q) (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (hT : 240 * (8 * (C : ℤ)) ^ 2 ≤ T)
    (hK : 1601 * (8 * (C : ℤ)) ^ 2 * ((highVertices q G).card + 1) ≤ K)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∉ lowHubs q T G) : signedDeficiency q G v ≤ K := by
  apply deficiency_le_off_lowHubs q T K (Nat.cast_nonneg K) G _ v hv
  intro w hw
  have hLarge : 1601 * (8 * (C : ℤ)) ^ 2 * ((highVertices q G).card + 1) ≤ signedDeficiency q G w := by omega
  have hMany := growing_deficiency_forces_low_neighbors q C hC G hFree hDegree hDense hq hHigh hNoCheap w hLarge
  have hScale := mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G w).card)
  omega

/-- Outside the low hub closure, both the local deficiency and neighboring positive weight are controlled. -/
theorem outside_lowHubClosure_bounds {n : ℕ} (q T : ℕ) (K : ℤ)
    (G : SimpleGraph (Fin n)) (hOutside : ∀ v, v ∉ lowHubs q T G → signedDeficiency q G v ≤ K)
    (l : Fin n) (hLow : l ∈ lowVertices q G) (hl : l ∉ lowHubClosure q T G) :
    signedDeficiency q G l ≤ K ∧
      (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) ≤ K * (lowNeighbors q G l).card ∧
      T * ((lowNeighbors q G l).card : ℤ) < q := by
  have hNotHub : l ∉ lowHubs q T G := fun h => hl (Finset.mem_union_left _ h)
  have hNeighborNotHub (w) (hw : w ∈ G.neighborFinset l) : w ∉ lowHubs q T G := by
    intro h
    have hlw : l ∈ G.neighborFinset w :=
      (G.mem_neighborFinset w l).mpr ((G.mem_neighborFinset l w).mp hw).symm
    exact hl (Finset.mem_union_right _ (Finset.mem_inter.mpr
      ⟨hLow, Finset.mem_biUnion.mpr ⟨w, h, hlw⟩⟩))
  refine ⟨hOutside l hNotHub, ?_, ?_⟩
  · have hEach (w) (hw : w ∈ lowNeighbors q G l) : signedDeficiency q G w ≤ K :=
      hOutside w (hNeighborNotHub w (Finset.mem_filter.mp hw).1)
    have hSum := Finset.sum_le_sum hEach
    rw [sum_lowNeighbors_deficiency] at hSum
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hSum
  · by_contra h
    exact hNotHub (Finset.mem_filter.mpr ⟨hLow, by omega⟩)

/-- Few vertices in one graph neighborhood can all have large low positive rows with small overlaps. -/
theorem large_low_partner_neighbors_card_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (x : Fin (q ^ 2 + q + 2))
    (A : Finset (Fin (q ^ 2 + q + 2))) (hA : A ⊆ G.neighborFinset x)
    (K J B : ℤ) (hK : 1 ≤ K) (hJ : 0 ≤ J) (hB : 1 ≤ B) (hq : 0 < q)
    (hLow : ∀ v ∈ A, 1 ≤ signedDeficiency q G v)
    (hBound : ∀ v ∈ A, signedDeficiency q G v ≤ K)
    (hWeight : ∀ v ∈ A, (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ J)
    (hLarge : ∀ v ∈ A, (q : ℤ) ≤ B * (lowPositivePartners q G v).card)
    (hSize : ((lowVertices q G).card : ℤ) ≤ 3 * q)
    (hGap : 6 * B ^ 2 * (2 + K ^ 2 + 2 * J) ≤ q) : (A.card : ℤ) ≤ 18 * B ^ 2 := by
  apply finite_family_card_le A (lowVertices q G) (fun v => lowPositivePartners q G v)
    q B (2 + K ^ 2 + 2 * J) (by exact_mod_cast hq) hB (by positivity) _ hSize hLarge _ hGap
  · intro v _ w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩
  · intro v hv w hw hvw
    have hCommon : 0 < codegree G v w := by
      apply Finset.card_pos.mpr
      exact ⟨x, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset v x).mpr ((G.mem_neighborFinset x v).mp (hA hv)).symm,
        (G.mem_neighborFinset w x).mpr ((G.mem_neighborFinset x w).mp (hA hw)).symm⟩⟩
    have hCodegree : codegree G v w = 1 := by
      have h := codegree_le_one G hFree v w hvw
      omega
    have hNonhigh (z) (hz : z ∈ lowVertices q G) : 0 ≤ signedDeficiency q G z := by
      have h := (Finset.mem_filter.mp hz).2
      omega
    have hOverlap := nonhigh_positivePartners_overlap_le q G hFree hDegree (lowVertices q G)
      hNonhigh v w (hLow v hv) (hLow w hw) hvw hCodegree
    have hSet : lowPositivePartners q G v ∩ lowPositivePartners q G w =
        lowVertices q G ∩ positivePartners q G v ∩ positivePartners q G w := by
      ext z
      simp [lowPositivePartners, lowVertices, and_assoc, and_left_comm, and_comm]
    rw [← hSet] at hOverlap
    have hProduct := mul_le_mul (hBound v hv) (hBound w hw) (by have h := hLow w hw; omega) (by omega)
    nlinarith only [hOverlap, hProduct, hWeight v hv, hWeight w hw]

/-- Adjacent unit lows force positive-row coverage of every untriangulated regular neighbor. -/
theorem adjacent_unit_positive_cover {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l w v : Fin n)
    (hLW : G.Adj l w) (hLV : G.Adj l v)
    (hL : signedDeficiency q G l = 1) (hW : signedDeficiency q G w = 1)
    (hV : signedDeficiency q G v = 0) (hUntri : codegree G l v = 0) :
    ∃ z ∈ G.neighborFinset v, z ∈ positivePartners q G w := by
  have hWV : w ≠ v := by intro h; subst v; omega
  have hNotWV : ¬G.Adj w v := by
    intro h
    exact (codegree_eq_zero_iff G l v).mp hUntri w hLW h.symm
  have hCommon : 0 < codegree G w v := by
    apply Finset.card_pos.mpr
    exact ⟨l, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w l).mpr hLW.symm,
      (G.mem_neighborFinset v l).mpr hLV.symm⟩⟩
  have hCodegree : codegree G w v = 1 := by
    have h := codegree_le_one G hFree w v hWV
    omega
  have hZWV : weightedResidual q G w v = 0 := by
    rw [weightedResidual_nonadj q G w v hWV hNotWV, hCodegree]
    norm_num
  have hZLV : weightedResidual q G l v = 0 := by
    rw [weightedResidual_off_diagonal q G l v hLV.ne, adjMatrix_square_codegree]
    simp only [G.adjMatrix_apply, ite_eq_left hLV, hUntri, hL, hV]
    norm_num
  have hZWL : weightedResidual q G w l ≤ -1 := by
    rw [weightedResidual_off_diagonal q G w l hLW.symm.ne, adjMatrix_square_codegree]
    simp only [G.adjMatrix_apply, ite_eq_left hLW.symm, hL, hW]
    have hNonneg : (0 : ℤ) ≤ codegree G w l := by positivity
    omega
  have hLNW : l ∈ G.neighborFinset w := (G.mem_neighborFinset w l).mpr hLW.symm
  have hLNV : l ∈ G.neighborFinset v := (G.mem_neighborFinset v l).mpr hLV.symm
  have hLeftRest : 0 ≤ ∑ z ∈ (G.neighborFinset w).erase l, weightedResidual q G z v := by
    apply Finset.sum_nonneg
    intro z hz
    have hZL := (Finset.mem_erase.mp hz).1
    have hWZ := (G.mem_neighborFinset w z).mp (Finset.mem_erase.mp hz).2
    have hZV : z ≠ v := by intro h; subst z; exact hNotWV hWZ
    have hNotZV : ¬G.Adj z v := by
      intro h
      have hEq := common_neighbor_unique G hFree hWV hLW.symm hLV.symm hWZ h.symm
      exact hZL hEq.symm
    exact weightedResidual_nonadj_nonnegative q G hFree z v hZV hNotZV
  have hLeft := Finset.sum_erase_add (G.neighborFinset w)
    (fun z => weightedResidual q G z v) hLNW
  rw [hZLV] at hLeft
  have hLeftBound : 0 ≤ ∑ z ∈ G.neighborFinset w, weightedResidual q G z v := by linarith
  by_contra hNone
  push Not at hNone
  have hRightRest : (∑ z ∈ (G.neighborFinset v).erase l, weightedResidual q G w z) ≤ 0 := by
    apply Finset.sum_nonpos
    intro z hz
    have hNot := hNone z (Finset.mem_erase.mp hz).2
    have hNonpos : ¬0 < weightedResidual q G w z := by
      intro h
      exact hNot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have hRight := Finset.sum_erase_add (G.neighborFinset v)
    (fun z => weightedResidual q G w z) hLNV
  have hRightBound : (∑ z ∈ G.neighborFinset v, weightedResidual q G w z) ≤ -1 := by linarith
  have hComm := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M w v)
    (weightedAdjacency_commutes_residual q G)
  simp only [weightedAdjacency_mul_apply, mul_weightedAdjacency_apply,
    hW, hV, hZWV, mul_zero, add_zero] at hComm
  linarith

/-- The positive row of one unit low covers the untriangulated regular neighbors of an adjacent unit low injectively. -/
theorem adjacent_unit_untriangulated_card_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l w : Fin (q ^ 2 + q + 2)) (hLW : G.Adj l w)
    (hL : signedDeficiency q G l = 1) (hW : signedDeficiency q G w = 1) :
    (regularNeighbors q G l).card - (triangularRegularNeighbors q G l).card ≤
      (positivePartners q G w).card := by
  let U := regularNeighbors q G l \ triangularRegularNeighbors q G l
  have hCover (v) (hv : v ∈ U) : ∃ z ∈ positivePartners q G w, G.Adj z v := by
    obtain ⟨hLV, hV, hUntri⟩ := untriangulated_regular_neighbor q G hFree l v hv
    obtain ⟨z, hz, hPositive⟩ := adjacent_unit_positive_cover q G hFree l w v hLW hLV hL hW hV hUntri
    exact ⟨z, hPositive, ((G.mem_neighborFinset v z).mp hz).symm⟩
  let cover := fun v => if hv : v ∈ U then (hCover v hv).choose else w
  have hSpec (v) (hv : v ∈ U) : cover v ∈ positivePartners q G w ∧ G.Adj (cover v) v := by
    dsimp only [cover]
    rw [dite_eq_left hv]
    exact (hCover v hv).choose_spec
  have hNotL : l ∉ positivePartners q G w := by
    intro h
    have hPositive := (Finset.mem_filter.mp h).2
    have hEntry := weightedResidual_off_diagonal q G w l hLW.symm.ne
    rw [adjMatrix_square_codegree] at hEntry
    simp only [G.adjMatrix_apply, ite_eq_left hLW.symm, hL, hW] at hEntry
    have hNonneg : (0 : ℤ) ≤ codegree G w l := by positivity
    omega
  have hCount : U.card ≤ (positivePartners q G w).card := by
    apply Finset.card_le_card_of_injOn cover
    · intro v hv
      exact (hSpec v hv).1
    · intro v hv x hx hEqual
      have hLV := (untriangulated_regular_neighbor q G hFree l v hv).1
      have hLX := (untriangulated_regular_neighbor q G hFree l x hx).1
      have hCV := (hSpec v hv).2
      have hCX := (hSpec x hx).2
      rw [← hEqual] at hCX
      have hDistinct : l ≠ cover v := by
        intro h
        exact hNotL (h ▸ (hSpec v hv).1)
      exact common_neighbor_unique G hFree hDistinct hLV hCV hLX hCX
  have hSubset : triangularRegularNeighbors q G l ⊆ regularNeighbors q G l := Finset.filter_subset _ _
  have hCard := Finset.card_sdiff_add_card_eq_card hSubset
  change U.card + (triangularRegularNeighbors q G l).card = (regularNeighbors q G l).card at hCard
  omega

/-- A unit low with few low neighbors has at most sixteen triangular regular neighbors on the light side of the dichotomy. -/
theorem light_unit_triangle_bound (q : ℕ) (hq : 0 < q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hUnit : signedDeficiency q G l = 1)
    (hFew : 8 * ((lowNeighbors q G l).card : ℤ) ≤ q)
    (hHigh : 8 * (((highVertices q G).card : ℤ) + 1) ≤ q)
    (hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * q)
    (hLight : 2 * ((triangularRegularNeighbors q G l).card : ℤ) ≤ q) :
    (triangularRegularNeighbors q G l).card ≤ 16 := by
  let u : ℤ := (triangularRegularNeighbors q G l).card
  let r : ℤ := (regularNeighbors q G l).card
  let δ : ℤ := (lowNeighbors q G l).card
  let h : ℤ := (highVertices q G).card
  have hDegree : (G.degree l : ℤ) = q := by unfold signedDeficiency at hUnit; omega
  have hLower := regular_neighbor_card_lower q G l
  change (G.degree l : ℤ) - δ - h ≤ r at hLower
  rw [hDegree] at hLower
  have hCover := triangle_cover_bound q G hFree l (by omega)
  rw [hUnit, hDegree, one_mul] at hCover
  change u * (r - u - 1) ≤ (q : ℤ) + _ at hCover
  change 8 * δ ≤ (q : ℤ) at hFew
  change 8 * (h + 1) ≤ (q : ℤ) at hHigh
  change 2 * u ≤ (q : ℤ) at hLight
  have hCoefficient : (q : ℤ) ≤ 4 * (r - u - 1) := by omega
  have hScaled := mul_le_mul_of_nonneg_left hCoefficient (show 0 ≤ u by dsimp [u]; positivity)
  have hFinal : u * q ≤ 16 * (q : ℤ) := by nlinarith only [hScaled, hCover, hTotal]
  have hqInt : (0 : ℤ) < q := by exact_mod_cast hq
  have hu : u ≤ 16 := (mul_le_mul_iff_of_pos_right hqInt).mp hFinal
  dsimp [u] at hu
  exact_mod_cast hu

/-- The positive row of a light unit low is controlled by its low degree and neighboring weight. -/
theorem unit_positivePartners_card_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hUnit : signedDeficiency q G l = 1)
    (hTriangles : (triangularRegularNeighbors q G l).card ≤ 16) (K : ℤ)
    (hWeight : (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) ≤ K * (lowNeighbors q G l).card) :
    ((positivePartners q G l).card : ℤ) ≤
      17 + (K + 1) * (lowNeighbors q G l).card + (highVertices q G).card := by
  have hRow := low_positivePartners_card_upper q G hFree l (by omega)
  rw [hUnit, triangle_codegree_sum_eq_card G hFree l] at hRow
  have hTriangle := (triangular_neighbor_card_bounds q G l).2
  have hTriangleInt : ((triangularNeighbors G l).card : ℤ) ≤
      (triangularRegularNeighbors q G l).card + (lowNeighbors q G l).card + (highVertices q G).card := by
    exact_mod_cast hTriangle
  have hBound : ((triangularRegularNeighbors q G l).card : ℤ) ≤ 16 := by exact_mod_cast hTriangles
  nlinarith only [hRow, hTriangleInt, hBound, hWeight]

theorem unit_untriangulated_regular_card_lower (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (l : Fin (q ^ 2 + q + 2))
    (hUnit : signedDeficiency q G l = 1)
    (hTriangles : (triangularRegularNeighbors q G l).card ≤ 16) :
    (q : ℤ) - (lowNeighbors q G l).card - (highVertices q G).card - 16 ≤
      ((regularNeighbors q G l \ triangularRegularNeighbors q G l).card : ℤ) := by
  have hDegree : (G.degree l : ℤ) = q := by unfold signedDeficiency at hUnit; omega
  have hLower := regular_neighbor_card_lower q G l
  rw [hDegree] at hLower
  have hSubset : triangularRegularNeighbors q G l ⊆ regularNeighbors q G l := Finset.filter_subset _ _
  have hPartition : ((regularNeighbors q G l \ triangularRegularNeighbors q G l).card : ℤ) +
      (triangularRegularNeighbors q G l).card = (regularNeighbors q G l).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hSubset
  have hBound : ((triangularRegularNeighbors q G l).card : ℤ) ≤ 16 := by exact_mod_cast hTriangles
  omega

/-- Adjacency between two unit lows requires a large combined low-neighbor contribution. -/
theorem adjacent_light_unit_degree_bound (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l w : Fin (q ^ 2 + q + 2)) (hAdj : G.Adj l w)
    (hL : signedDeficiency q G l = 1) (hW : signedDeficiency q G w = 1)
    (hTL : (triangularRegularNeighbors q G l).card ≤ 16)
    (hTW : (triangularRegularNeighbors q G w).card ≤ 16) (K : ℤ)
    (hWeight : (∑ v ∈ G.neighborFinset w, positiveDeficiency q G v) ≤ K * (lowNeighbors q G w).card) :
    (q : ℤ) ≤ (lowNeighbors q G l).card + (K + 1) * (lowNeighbors q G w).card +
      2 * (highVertices q G).card + 33 := by
  have hCover := adjacent_unit_untriangulated_card_le q G hFree l w hAdj hL hW
  have hSubset : triangularRegularNeighbors q G l ⊆ regularNeighbors q G l := Finset.filter_subset _ _
  have hPartition := Finset.card_sdiff_add_card_eq_card hSubset
  have hCoverInt : ((regularNeighbors q G l \ triangularRegularNeighbors q G l).card : ℤ) ≤
      (positivePartners q G w).card := by
    have hNat : (regularNeighbors q G l \ triangularRegularNeighbors q G l).card ≤
        (positivePartners q G w).card := by omega
    exact_mod_cast hNat
  have hLower := unit_untriangulated_regular_card_lower q G l hL hTL
  have hUpper := unit_positivePartners_card_le q G hFree w hW hTW K hWeight
  omega

/-- Sparse light unit lows form an independent vertex set. -/
theorem light_unit_set_independent (q : ℕ) (hq : 0 < q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (L : Finset (Fin (q ^ 2 + q + 2))) (K : ℤ) (hK : 0 ≤ K)
    (hUnit : ∀ v ∈ L, signedDeficiency q G v = 1)
    (hTriangles : ∀ v ∈ L, (triangularRegularNeighbors q G v).card ≤ 16)
    (hWeight : ∀ v ∈ L, (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ K * (lowNeighbors q G v).card)
    (hFew : ∀ v ∈ L, 8 * (K + 1) * (lowNeighbors q G v).card ≤ q)
    (hHigh : 4 * (2 * ((highVertices q G).card : ℤ) + 33) ≤ q) :
    ∀ l ∈ L, ∀ w ∈ L, ¬G.Adj l w := by
  intro l hl w hw hAdj
  have hBound := adjacent_light_unit_degree_bound q G hFree l w hAdj (hUnit l hl) (hUnit w hw)
    (hTriangles l hl) (hTriangles w hw) K (hWeight w hw)
  have hFewL := hFew l hl
  have hFewW := hFew w hw
  have hBasicL : 8 * ((lowNeighbors q G l).card : ℤ) ≤ q := by
    have hExtra := mul_nonneg hK (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G l).card)
    nlinarith only [hFewL, hExtra]
  have hqInt : (0 : ℤ) < q := by exact_mod_cast hq
  nlinarith only [hBound, hBasicL, hFewW, hHigh, hqInt]

def lightLowVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (lowVertices q G \ lowHubClosure q T G).filter fun v =>
    signedDeficiency q G v = 1 ∧ 2 * ((triangularRegularNeighbors q G v).card : ℤ) < q

/-- The light lows outside the hub closure are independent under the uniform local hypotheses. -/
theorem lightLowVertices_independent (q T : ℕ) (hq : 0 < q) (K : ℤ) (hK : 0 ≤ K)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hOutside : ∀ v, v ∉ lowHubs q T G → signedDeficiency q G v ≤ K)
    (hT : 8 * (K + 1) ≤ T)
    (hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * q)
    (hHigh : 4 * (2 * ((highVertices q G).card : ℤ) + 33) ≤ q) :
    ∀ l ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj l w := by
  have hSpec (v) (hv : v ∈ lightLowVertices q T G) :
      signedDeficiency q G v = 1 ∧
      (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ K * (lowNeighbors q G v).card ∧
      8 * (K + 1) * (lowNeighbors q G v).card ≤ (q : ℤ) ∧
      (triangularRegularNeighbors q G v).card ≤ 16 := by
    obtain ⟨hvOutside, hvUnit, hvLight⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvLow, hvNot⟩ := Finset.mem_sdiff.mp hvOutside
    obtain ⟨_, hWeight, hFew⟩ := outside_lowHubClosure_bounds q T K G hOutside v hvLow hvNot
    have hFewScaled := mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G v).card)
    have hFewFinal : 8 * (K + 1) * (lowNeighbors q G v).card ≤ (q : ℤ) := by omega
    have hBasic : 8 * ((lowNeighbors q G v).card : ℤ) ≤ (q : ℤ) := by
      have hExtra := mul_nonneg hK (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G v).card)
      nlinarith only [hFewFinal, hExtra]
    have hHighBasic : 8 * (((highVertices q G).card : ℤ) + 1) ≤ (q : ℤ) := by omega
    have hTriangles := light_unit_triangle_bound q hq G hFree v hvUnit hBasic hHighBasic hTotal (by omega)
    exact ⟨hvUnit, hWeight, hFewFinal, hTriangles⟩
  exact light_unit_set_independent q hq G hFree (lightLowVertices q T G) K hK
    (fun v hv => (hSpec v hv).1) (fun v hv => (hSpec v hv).2.2.2)
    (fun v hv => (hSpec v hv).2.1) (fun v hv => (hSpec v hv).2.2.1) hHigh

def activeLowVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (lowVertices q G \ lowHubClosure q T G).filter fun v =>
    2 ≤ signedDeficiency q G v ∨ (q : ℤ) ≤ 2 * (triangularRegularNeighbors q G v).card

/-- The bounded local estimate applies uniformly to active lows outside the hub closure. -/
theorem active_low_many_partners (q C K T : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (hOutside : ∀ v, v ∉ lowHubs q T G → signedDeficiency q G v ≤ K)
    (D : ℤ) (hD : D = 400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3)
    (hT : 16 * D * ((K : ℤ) + 1) ≤ T) (hq : 16 * D ≤ q)
    (hSize : 16 * ((K : ℤ) + 4) ^ 2 * (16 * D) ^ 3 ≤ q)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ activeLowVertices q T G) :
    (q : ℤ) ≤ 2 * D * (lowPositivePartners q G v).card := by
  obtain ⟨hvOutside, hvActive⟩ := Finset.mem_filter.mp hv
  obtain ⟨hvLow, hvNot⟩ := Finset.mem_sdiff.mp hvOutside
  have hLow : 1 ≤ signedDeficiency q G v := by
    have h := (Finset.mem_filter.mp hvLow).2
    omega
  obtain ⟨hBound, hWeight, hFew⟩ := outside_lowHubClosure_bounds q T K G hOutside v hvLow hvNot
  have hKInt : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
  have hDPos : 0 < D := by rw [hD]; positivity
  have hDelta : (0 : ℤ) ≤ (lowNeighbors q G v).card := by positivity
  have hc : 0 ≤ ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w :=
    Finset.sum_nonneg (fun w _ => positiveDeficiency_nonnegative q G w)
  have hWeightScaled := mul_le_mul_of_nonneg_left hWeight (show 0 ≤ 16 * D by omega)
  have hThresholdScaled := mul_le_mul_of_nonneg_right hT hDelta
  have hLocalSmall : 16 * D * ((∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) +
      (lowNeighbors q G v).card) ≤ (q : ℤ) := by
    nlinarith only [hWeightScaled, hThresholdScaled, hFew]
  have hSparse : 8 * D * (1 + (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) +
      (lowNeighbors q G v).card) ≤ (q : ℤ) := by nlinarith only [hLocalSmall, hq]
  have hNeighborWeight : (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ (q : ℤ) := by
    have hExtra := mul_nonneg (show 0 ≤ 16 * D - 1 by omega) hc
    have hDeltaExtra := mul_nonneg (show 0 ≤ 16 * D by omega) hDelta
    nlinarith only [hLocalSmall, hExtra, hDeltaExtra]
  have hResult := bounded_deficiency_many_low_partners q C K hC hK hKq G hFree hDegree hDense
    hHigh hNoCheap v hLow hBound hNeighborWeight hvActive
    (by simpa only [hD] using hSparse) (by simpa only [hD] using hSize)
  simpa only [hD] using hResult

/-- A fixed overlap gap bounds the number of active lows seen at every graph vertex. -/
theorem activeLowVertices_neighbor_card_le (q C K T : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (hOutside : ∀ v, v ∉ lowHubs q T G → signedDeficiency q G v ≤ K)
    (D : ℤ) (hD : D = 400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3)
    (hT : 16 * D * ((K : ℤ) + 1) ≤ T) (hq : 16 * D ≤ q)
    (hSize : 16 * ((K : ℤ) + 4) ^ 2 * (16 * D) ^ 3 ≤ q)
    (hOverlapT : 24 * (2 * D) ^ 2 * K ≤ T)
    (hOverlapQ : 12 * (2 * D) ^ 2 * (2 + (K : ℤ) ^ 2) ≤ q)
    (x : Fin (q ^ 2 + q + 2)) :
    ((G.neighborFinset x ∩ activeLowVertices q T G).card : ℤ) ≤ 18 * (2 * D) ^ 2 := by
  let A := G.neighborFinset x ∩ activeLowVertices q T G
  let B := 2 * D
  let J := (K : ℤ) * q / T
  have hKInt : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
  have hDPos : 0 < D := by rw [hD]; positivity
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hTPos : (0 : ℤ) < T := by
    have hPositive : 0 < 16 * D * ((K : ℤ) + 1) := by positivity
    omega
  have hJ : 0 ≤ J := Int.ediv_nonneg (by positivity) (le_of_lt hTPos)
  have hqNat : 0 < q := by omega
  have hLow (v) (hv : v ∈ A) : 1 ≤ signedDeficiency q G v := by
    have h := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).1).1
    have hPositive := (Finset.mem_filter.mp h).2
    omega
  have hSpec (v) (hv : v ∈ A) : signedDeficiency q G v ≤ K ∧
      (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ J := by
    have hvAct := (Finset.mem_inter.mp hv).2
    have hvLow := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvAct).1).1
    have hvNot := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvAct).1).2
    obtain ⟨hBound, hWeight, hFew⟩ := outside_lowHubClosure_bounds q T K G hOutside v hvLow hvNot
    refine ⟨hBound, ?_⟩
    apply (Int.le_ediv_iff_mul_le hTPos).mpr
    have h1 := mul_le_mul_of_nonneg_left hWeight (le_of_lt hTPos)
    have h2 := mul_le_mul_of_nonneg_left hFew.le (show 0 ≤ (K : ℤ) by omega)
    nlinarith only [h1, h2]
  have hLarge (v) (hv : v ∈ A) : (q : ℤ) ≤ B * (lowPositivePartners q G v).card :=
    active_low_many_partners q C K T hC hK hKq G hFree hDegree hDense hHigh hNoCheap
      hOutside D hD hT hq hSize v (Finset.mem_inter.mp hv).2
  have hTJ : (T : ℤ) * J ≤ (K : ℤ) * q := Int.mul_ediv_self_le (ne_of_gt hTPos)
  have hOverlapScaled := mul_le_mul_of_nonneg_right hOverlapT hJ
  have hVariable : 24 * B ^ 2 * J ≤ (q : ℤ) := by
    apply (mul_le_mul_iff_of_pos_left (show (0 : ℤ) < K by omega)).mp
    dsimp only [B]
    linear_combination hTJ + hOverlapScaled
  have hGap : 6 * B ^ 2 * (2 + (K : ℤ) ^ 2 + 2 * J) ≤ (q : ℤ) := by
    change 12 * B ^ 2 * (2 + (K : ℤ) ^ 2) ≤ (q : ℤ) at hOverlapQ
    nlinarith only [hVariable, hOverlapQ]
  exact large_low_partner_neighbors_card_le q G hFree hDegree x A Finset.inter_subset_left K J B hKInt hJ hB
    hqNat hLow (fun v hv => (hSpec v hv).1) (fun v hv => (hSpec v hv).2) hLarge
    (dense_lowVertices_card_le q G hDegree hDense hHigh) hGap

def nonlightLowVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  lowVertices q G \ lightLowVertices q T G

/-- Every nonlight low is in the hub closure or is active. -/
theorem nonlightLowVertices_subset {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) :
    nonlightLowVertices q T G ⊆ lowHubClosure q T G ∪ activeLowVertices q T G := by
  intro v hv
  obtain ⟨hvLow, hvNotLight⟩ := Finset.mem_sdiff.mp hv
  by_cases hvClosure : v ∈ lowHubClosure q T G
  · exact Finset.mem_union_left _ hvClosure
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hvLow, hvClosure⟩, ?_⟩
    have hPositive := (Finset.mem_filter.mp hvLow).2
    by_cases hUnit : signedDeficiency q G v = 1
    · apply Or.inr
      by_contra h
      exact hvNotLight (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvLow, hvClosure⟩, hUnit, by omega⟩)
    · exact Or.inl (by omega)

/-- Away from the hubs, the nonlight low degree is bounded by the hub and active contributions. -/
theorem nonlight_neighbor_card_le {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (v : Fin n) (hv : v ∉ lowHubs q T G)
    (B : ℤ) (hActive : ((G.neighborFinset v ∩ activeLowVertices q T G).card : ℤ) ≤ B) :
    ((G.neighborFinset v ∩ nonlightLowVertices q T G).card : ℤ) ≤
      2 * (lowHubs q T G).card + B := by
  have hCover : G.neighborFinset v ∩ nonlightLowVertices q T G ⊆
      (G.neighborFinset v ∩ lowHubClosure q T G) ∪
        (G.neighborFinset v ∩ activeLowVertices q T G) := by
    intro w hw
    obtain ⟨hwN, hwNonlight⟩ := Finset.mem_inter.mp hw
    rcases Finset.mem_union.mp (nonlightLowVertices_subset q T G hwNonlight) with hwC | hwA
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hwN, hwC⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hwN, hwA⟩)
  have hCard := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hCardInt : ((G.neighborFinset v ∩ nonlightLowVertices q T G).card : ℤ) ≤
      (G.neighborFinset v ∩ lowHubClosure q T G).card + (G.neighborFinset v ∩ activeLowVertices q T G).card := by
    exact_mod_cast hCard
  have hClosure : ((G.neighborFinset v ∩ lowHubClosure q T G).card : ℤ) ≤ 2 * (lowHubs q T G).card := by
    exact_mod_cast lowHubClosure_neighbor_card_le q T G hFree v hv
  omega

/-- Independence converts the low degree of a light vertex to its nonlight low degree. -/
theorem light_lowNeighbors_eq_nonlight {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (hIndependent : ∀ l ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj l w)
    (l : Fin n) (hl : l ∈ lightLowVertices q T G) :
    lowNeighbors q G l = G.neighborFinset l ∩ nonlightLowVertices q T G := by
  rw [lowNeighbors_eq_inter]
  ext w
  simp only [Finset.mem_inter, nonlightLowVertices, Finset.mem_sdiff]
  constructor
  · rintro ⟨hwN, hwLow⟩
    refine ⟨hwN, hwLow, ?_⟩
    intro hwLight
    exact hIndependent l hl w hwLight ((G.mem_neighborFinset l w).mp hwN)
  · rintro ⟨hwN, hwLow, _⟩
    exact ⟨hwN, hwLow⟩

theorem light_low_degree_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hIndependent : ∀ l ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj l w)
    (l : Fin (q ^ 2 + q + 2)) (hl : l ∈ lightLowVertices q T G)
    (B : ℤ) (hActive : ((G.neighborFinset l ∩ activeLowVertices q T G).card : ℤ) ≤ B) :
    ((lowNeighbors q G l).card : ℤ) ≤ 2 * (lowHubs q T G).card + B := by
  have hNotClosure := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hl).1).2
  have hNotHub : l ∉ lowHubs q T G := fun h => hNotClosure (Finset.mem_union_left _ h)
  rw [light_lowNeighbors_eq_nonlight q T G hIndependent l hl]
  exact nonlight_neighbor_card_le q T G hFree l hNotHub B hActive

/-- The positive residual row of a light vertex has a constant bound once nonlight incidences are bounded. -/
theorem light_positivePartners_card_bound (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (K : ℤ) (hK : 0 ≤ K)
    (hOutside : ∀ v, v ∉ lowHubs q T G → signedDeficiency q G v ≤ K)
    (hIndependent : ∀ l ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj l w)
    (l : Fin (q ^ 2 + q + 2)) (hl : l ∈ lightLowVertices q T G)
    (hTriangles : (triangularRegularNeighbors q G l).card ≤ 16)
    (B : ℤ) (hActive : ((G.neighborFinset l ∩ activeLowVertices q T G).card : ℤ) ≤ B) :
    ((positivePartners q G l).card : ℤ) ≤
      17 + (K + 1) * (2 * (lowHubs q T G).card + B) + (highVertices q G).card := by
  obtain ⟨hlOutside, hlUnit, _⟩ := Finset.mem_filter.mp hl
  obtain ⟨hlLow, hlNot⟩ := Finset.mem_sdiff.mp hlOutside
  have hWeight := (outside_lowHubClosure_bounds q T K G hOutside l hlLow hlNot).2.1
  have hRow := unit_positivePartners_card_le q G hFree l hlUnit hTriangles K hWeight
  have hDegree := light_low_degree_le q T G hFree hIndependent l hl B hActive
  have hScaled := mul_le_mul_of_nonneg_left hDegree (show 0 ≤ K + 1 by omega)
  omega

def lightTriangleRegularVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (lightLowVertices q T G).biUnion (fun l => triangularRegularNeighbors q G l)

def multipleHubCenters {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => 2 ≤ (G.neighborFinset v ∩ lowHubs q T G).card

theorem lightTriangleRegularVertices_regular {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) (hv : v ∈ lightTriangleRegularVertices q T G) : signedDeficiency q G v = 0 := by
  obtain ⟨l, _, hlv⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hlv).1).2

theorem lightTriangleRegularVertices_not_hub {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) (hv : v ∈ lightTriangleRegularVertices q T G) : v ∉ lowHubs q T G := by
  have hZero := lightTriangleRegularVertices_regular q T G v hv
  intro h
  have hPositive := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
  omega

/-- An exceptional regular vertex has nearly q units of neighboring positive deficiency. -/
theorem light_triangle_neighbor_weight_lower (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (d : ℤ) (hLowDegree : ∀ l ∈ lightLowVertices q T G, ((lowNeighbors q G l).card : ℤ) ≤ d)
    (hTriangles : ∀ l ∈ lightLowVertices q T G, (triangularRegularNeighbors q G l).card ≤ 16)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ lightTriangleRegularVertices q T G) :
    (q : ℤ) - d - (highVertices q G).card - 17 ≤
      ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  obtain ⟨l, hl, hlv⟩ := Finset.mem_biUnion.mp hv
  have hUnit := (Finset.mem_filter.mp hl).2.1
  have hDegree : (G.degree l : ℤ) = q := by unfold signedDeficiency at hUnit; omega
  have hRegular := regular_neighbor_card_lower q G l
  rw [hDegree] at hRegular
  have hCover := triangular_regular_neighbor_cover_bound q G hFree l (by omega) v hlv
  have hTri : ((triangularRegularNeighbors q G l).card : ℤ) ≤ 16 := by exact_mod_cast hTriangles l hl
  have hLow := hLowDegree l hl
  omega

/-- Count a constant weight over neighbors lying in a selected set. -/
theorem neighbor_indicator_weight_sum {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (S : Finset (Fin n)) (a : ℤ) :
    (∑ w ∈ G.neighborFinset v, if w ∈ S then a else 0) = a * (G.neighborFinset v ∩ S).card := by
  rw [← Finset.sum_filter]
  have hSet : ((G.neighborFinset v).filter fun w => w ∈ S) = G.neighborFinset v ∩ S := by
    ext w
    simp
  rw [hSet]
  simp [mul_comm]

/-- With at most one hub neighbor, positive deficiency is bounded by the light and nonlight incidences. -/
theorem neighbor_positive_weight_one_hub (q T R : ℕ) (hR : 1 ≤ R) (K : ℤ) (hK : 0 ≤ K)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (hMin : ∀ w, q ≤ R * G.degree w) (v : Fin (q ^ 2 + q + 2))
    (hOneHub : (G.neighborFinset v ∩ lowHubs q T G).card ≤ 1) :
    (R : ℤ) * (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤
      R * (G.neighborFinset v ∩ lightLowVertices q T G).card +
        R * K * (G.neighborFinset v ∩ nonlightLowVertices q T G).card + R * ((q : ℤ) + 1) - q := by
  let H : ℤ := R * ((q : ℤ) + 1) - q
  have hRInt : (1 : ℤ) ≤ R := by exact_mod_cast hR
  have hH : 0 ≤ H := by
    have h := mul_nonneg (show 0 ≤ (R : ℤ) - 1 by omega) (Nat.cast_nonneg (α := ℤ) q)
    dsimp [H]
    nlinarith only [h, hRInt]
  have hEach (w : Fin (q ^ 2 + q + 2)) : (R : ℤ) * positiveDeficiency q G w ≤
      (if w ∈ lightLowVertices q T G then (R : ℤ) else 0) +
        (if w ∈ nonlightLowVertices q T G then (R : ℤ) * K else 0) +
        (if w ∈ lowHubs q T G then H else 0) := by
    by_cases hwHub : w ∈ lowHubs q T G
    · have hBound := positiveDeficiency_scaled_le q R hR G w (hMin w)
      change (R : ℤ) * positiveDeficiency q G w ≤ H at hBound
      have hLightNonneg : 0 ≤ (if w ∈ lightLowVertices q T G then (R : ℤ) else 0) := by split <;> omega
      have hOtherNonneg : 0 ≤ (if w ∈ nonlightLowVertices q T G then (R : ℤ) * K else 0) := by
        split <;> positivity
      rw [ite_eq_left hwHub]
      linarith only [hBound, hLightNonneg, hOtherNonneg]
    · rw [ite_eq_right hwHub, add_zero]
      by_cases hwLight : w ∈ lightLowVertices q T G
      · have hUnit := (Finset.mem_filter.mp hwLight).2.1
        have hPositive : positiveDeficiency q G w = 1 := by simp [positiveDeficiency, hUnit]
        rw [ite_eq_left hwLight, hPositive, mul_one]
        have hOtherNonneg : 0 ≤ (if w ∈ nonlightLowVertices q T G then (R : ℤ) * K else 0) := by
          split <;> positivity
        linarith only [hOtherNonneg]
      · rw [ite_eq_right hwLight, zero_add]
        by_cases hwLow : 0 < signedDeficiency q G w
        · have hwNonlight : w ∈ nonlightLowVertices q T G := Finset.mem_sdiff.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwLow⟩, hwLight⟩
          have hBound := hOutside w hwHub
          have hPositive : positiveDeficiency q G w = signedDeficiency q G w := max_eq_left (by omega)
          rw [ite_eq_left hwNonlight, hPositive]
          exact mul_le_mul_of_nonneg_left hBound (by omega)
        · have hwNonlight : w ∉ nonlightLowVertices q T G := by
            intro h
            have hPositive := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
            exact hwLow hPositive
          have hPositive : positiveDeficiency q G w = 0 := max_eq_right (by omega)
          simp only [ite_eq_right hwNonlight, hPositive, mul_zero, le_refl]
  have hSum := Finset.sum_le_sum (fun w (_ : w ∈ G.neighborFinset v) => hEach w)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    neighbor_indicator_weight_sum, neighbor_indicator_weight_sum, neighbor_indicator_weight_sum] at hSum
  have hHubCard : ((G.neighborFinset v ∩ lowHubs q T G).card : ℤ) ≤ 1 := by exact_mod_cast hOneHub
  have hHubScale := mul_le_mul_of_nonneg_left hHubCard hH
  dsimp [H] at hSum hHubScale
  nlinarith only [hSum, hHubScale]

/-- Only boundedly many vertices can see two selected hubs. -/
theorem multipleHubCenters_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G) :
    (multipleHubCenters q T G).card ≤ (lowHubs q T G).card.choose 2 := by
  have hEach (v) (hv : v ∈ multipleHubCenters q T G) :
      1 ≤ (G.neighborFinset v ∩ lowHubs q T G).card.choose 2 := by
    exact Nat.succ_le_of_lt (Nat.choose_pos (Finset.mem_filter.mp hv).2)
  have hSum := Finset.sum_le_sum hEach
  have hCount := sum_choose_neighbors_in_set_le G hFree (multipleHubCenters q T G) (lowHubs q T G)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hSum
  exact hSum.trans hCount

/-- The regular endpoints of triangular light edges form a bounded exceptional set. -/
theorem lightTriangleRegularVertices_card_le (q T R : ℕ) (hR : 1 ≤ R)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (K d B : ℤ) (hK : 0 ≤ K)
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (hMin : ∀ w, q ≤ R * G.degree w)
    (hLowDegree : ∀ l ∈ lightLowVertices q T G, ((lowNeighbors q G l).card : ℤ) ≤ d)
    (hTriangles : ∀ l ∈ lightLowVertices q T G, (triangularRegularNeighbors q G l).card ≤ 16)
    (hNonlight : ∀ v, v ∉ lowHubs q T G → ((G.neighborFinset v ∩ nonlightLowVertices q T G).card : ℤ) ≤ B)
    (hLowSize : ((lowVertices q G).card : ℤ) ≤ 3 * q)
    (hOrder : 2 * (R : ℤ) * (d + (highVertices q G).card + K * B + 18) ≤ q)
    (hFamily : 6 * (2 * (R : ℤ)) ^ 2 ≤ q) :
    ((lightTriangleRegularVertices q T G).card : ℤ) ≤
      18 * (2 * (R : ℤ)) ^ 2 + ((lowHubs q T G).card.choose 2 : ℤ) := by
  let J := lightTriangleRegularVertices q T G
  let A := J \ multipleHubCenters q T G
  let L := lightLowVertices q T G
  have hRInt : (1 : ℤ) ≤ R := by exact_mod_cast hR
  have hq : (0 : ℤ) < q := by nlinarith only [hFamily, hRInt]
  have hLightSubset : L ⊆ lowVertices q G := by
    intro v hv
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hLightSize : (L.card : ℤ) ≤ 3 * q := by
    have hCard : (L.card : ℤ) ≤ (lowVertices q G).card := by exact_mod_cast Finset.card_le_card hLightSubset
    exact hCard.trans hLowSize
  have hMany (v) (hv : v ∈ A) : (q : ℤ) ≤ (2 * (R : ℤ)) * (G.neighborFinset v ∩ L).card := by
    obtain ⟨hvJ, hvNot⟩ := Finset.mem_sdiff.mp hv
    have hNotHub := lightTriangleRegularVertices_not_hub q T G v hvJ
    have hOneHub : (G.neighborFinset v ∩ lowHubs q T G).card ≤ 1 := by
      by_contra h
      exact hvNot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
    have hLower := light_triangle_neighbor_weight_lower q T G hFree d hLowDegree hTriangles v hvJ
    have hLowerScaled := mul_le_mul_of_nonneg_left hLower (show 0 ≤ (R : ℤ) by omega)
    have hUpper := neighbor_positive_weight_one_hub q T R hR K hK G hOutside hMin v hOneHub
    have hBound := hNonlight v hNotHub
    have hBoundScaled := mul_le_mul_of_nonneg_left hBound (show 0 ≤ (R : ℤ) * K by positivity)
    change (q : ℤ) ≤ 2 * R * (G.neighborFinset v ∩ lightLowVertices q T G).card
    nlinarith only [hLowerScaled, hUpper, hBoundScaled, hOrder]
  have hCount : (A.card : ℤ) ≤ 18 * (2 * (R : ℤ)) ^ 2 := by
    apply finite_family_card_le A L (fun v => G.neighborFinset v ∩ L) q (2 * R) 1 hq (by omega) (by norm_num)
    · intro v _
      exact Finset.inter_subset_right
    · exact hLightSize
    · exact hMany
    · intro v _ w _ hvw
      have hSubset : (G.neighborFinset v ∩ L) ∩ (G.neighborFinset w ∩ L) ⊆
          G.neighborFinset v ∩ G.neighborFinset w := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
      have hCard : (((G.neighborFinset v ∩ L) ∩ (G.neighborFinset w ∩ L)).card : ℤ) ≤
          (G.neighborFinset v ∩ G.neighborFinset w).card := by exact_mod_cast Finset.card_le_card hSubset
      have hCodegree : ((G.neighborFinset v ∩ G.neighborFinset w).card : ℤ) ≤ 1 := by
        exact_mod_cast codegree_le_one G hFree v w hvw
      exact hCard.trans hCodegree
    · simpa only [mul_one] using hFamily
  have hCover : J ⊆ A ∪ multipleHubCenters q T G := by
    intro v hv
    by_cases hBad : v ∈ multipleHubCenters q T G
    · exact Finset.mem_union_right _ hBad
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hBad⟩)
  have hCoverCount := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hCoverInt : (J.card : ℤ) ≤ A.card + (multipleHubCenters q T G).card := by exact_mod_cast hCoverCount
  have hBad : ((multipleHubCenters q T G).card : ℤ) ≤ (lowHubs q T G).card.choose 2 := by
    exact_mod_cast multipleHubCenters_card_le q T G hFree
  change (J.card : ℤ) ≤ _
  omega

def triangularLightNeighbors {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v).filter fun l => l ∈ lightLowVertices q T G ∧ codegree G v l = 1

theorem codegree_eq_one_of_common_vertex {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (x y z : Fin n) (hxy : x ≠ y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) : codegree G x y = 1 := by
  have hPositive : 0 < codegree G x y := by
    apply Finset.card_pos.mpr
    exact ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x z).mpr hxz, (G.mem_neighborFinset y z).mpr hyz⟩⟩
  have hUpper := codegree_le_one G hFree x y hxy
  omega

/-- The third vertex of a triangle on a light edge lies in the exceptional regular set, the high set, or the nonlight lows. -/
theorem triangular_light_neighbor_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hIndependent : ∀ l ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj l w)
    (v : Fin (q ^ 2 + q + 2)) :
    (triangularLightNeighbors q T G v).card ≤ (lightTriangleRegularVertices q T G).card +
      (highVertices q G).card + (G.neighborFinset v ∩ nonlightLowVertices q T G).card := by
  let S := triangularLightNeighbors q T G v
  have hThird (l) (hl : l ∈ S) : ∃ z, G.Adj v z ∧ G.Adj l z := by
    have hCodegree := (Finset.mem_filter.mp hl).2.2
    have hPositive : 0 < codegree G v l := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hPositive
    exact ⟨z, (G.mem_neighborFinset v z).mp (Finset.mem_inter.mp hz).1,
      (G.mem_neighborFinset l z).mp (Finset.mem_inter.mp hz).2⟩
  let third := fun l => if hl : l ∈ S then (hThird l hl).choose else v
  have hSpec (l) (hl : l ∈ S) : G.Adj v (third l) ∧ G.Adj l (third l) := by
    dsimp only [third]
    rw [dite_eq_left hl]
    exact (hThird l hl).choose_spec
  let P := lightTriangleRegularVertices q T G ∪ highVertices q G ∪
    (G.neighborFinset v ∩ nonlightLowVertices q T G)
  have hMaps (l) (hl : l ∈ S) : third l ∈ P := by
    have hlLight := (Finset.mem_filter.mp hl).2.1
    have hVL := (G.mem_neighborFinset v l).mp (Finset.mem_filter.mp hl).1
    obtain ⟨hVZ, hLZ⟩ := hSpec l hl
    have hzNotLight : third l ∉ lightLowVertices q T G := fun hz => hIndependent l hlLight (third l) hz hLZ
    by_cases hZero : signedDeficiency q G (third l) = 0
    · have hCodegree := codegree_eq_one_of_common_vertex G hFree l (third l) v hLZ.ne hVL.symm hVZ.symm
      have hzRegular : third l ∈ triangularRegularNeighbors q G l := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset l (third l)).mpr hLZ, hZero⟩, hCodegree⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨l, hlLight, hzRegular⟩))
    · by_cases hPositive : 0 < signedDeficiency q G (third l)
      · have hzNonlight : third l ∈ nonlightLowVertices q T G := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPositive⟩, hzNotLight⟩
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v (third l)).mpr hVZ, hzNonlight⟩)
      · have hzHigh : third l ∈ highVertices q G := (mem_highVertices_iff q G (third l)).mpr (by omega)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hzHigh)
  have hCount : S.card ≤ P.card := by
    apply Finset.card_le_card_of_injOn third hMaps
    intro l hl w hw hEqual
    have hVL := (G.mem_neighborFinset v l).mp (Finset.mem_filter.mp hl).1
    have hVW := (G.mem_neighborFinset v w).mp (Finset.mem_filter.mp hw).1
    have hZL := (hSpec l hl).2.symm
    have hZW := (hSpec w hw).2.symm
    rw [← hEqual] at hZW
    exact common_neighbor_unique G hFree (hSpec l hl).1.ne hVL hZL hVW hZW
  have hUnion := Finset.card_union_le (lightTriangleRegularVertices q T G ∪ highVertices q G)
    (G.neighborFinset v ∩ nonlightLowVertices q T G)
  have hFirst := Finset.card_union_le (lightTriangleRegularVertices q T G) (highVertices q G)
  change S.card ≤ _
  dsimp only [P] at hCount
  omega

theorem regular_negativeResidualMass_eq_neighbor_sum (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hRegular : signedDeficiency q G v = 0) :
    negativeResidualMass q G v = ∑ w ∈ G.neighborFinset v, max (-weightedResidual q G v w) 0 := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro w _ hw
  by_cases hEq : v = w
  · subst w
    simp [weightedResidual_diagonal, hRegular]
  · have hNot : ¬G.Adj v w := fun h => hw ((G.mem_neighborFinset v w).mpr h)
    have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree v w hEq hNot
    exact max_eq_right (by omega)

/-- At a regular vertex, a light neighbor contributes negative mass only along a triangular edge. -/
theorem regular_negativeResidualMass_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hRegular : signedDeficiency q G v = 0) :
    negativeResidualMass q G v ≤ (triangularLightNeighbors q T G v).card +
      ∑ w ∈ G.neighborFinset v ∩ nonlightLowVertices q T G, positiveDeficiency q G w := by
  have hEach (w) (hw : w ∈ G.neighborFinset v) : max (-weightedResidual q G v w) 0 ≤
      (if w ∈ triangularLightNeighbors q T G v then (1 : ℤ) else 0) +
        (if w ∈ nonlightLowVertices q T G then positiveDeficiency q G w else 0) := by
    have hAdj := (G.mem_neighborFinset v w).mp hw
    have hRow := weightedResidual_regular_neighbor q G v w hAdj hRegular
    have hCodegree : (codegree G v w : ℤ) ≤ 1 := by exact_mod_cast codegree_le_one G hFree v w hAdj.ne
    by_cases hwLight : w ∈ lightLowVertices q T G
    · have hUnit := (Finset.mem_filter.mp hwLight).2.1
      have hwNotNonlight : w ∉ nonlightLowVertices q T G := fun h => (Finset.mem_sdiff.mp h).2 hwLight
      rw [ite_eq_right hwNotNonlight, add_zero]
      by_cases hTri : codegree G v w = 1
      · have hwTri : w ∈ triangularLightNeighbors q T G v := Finset.mem_filter.mpr ⟨hw, hwLight, hTri⟩
        rw [ite_eq_left hwTri]
        rw [hUnit, hTri] at hRow
        norm_num at hRow
        rw [hRow]
        norm_num
      · have hZero : codegree G v w = 0 := by omega
        have hwNotTri : w ∉ triangularLightNeighbors q T G v := by
          intro h
          exact hTri (Finset.mem_filter.mp h).2.2
        rw [ite_eq_right hwNotTri]
        rw [hUnit, hZero] at hRow
        norm_num at hRow
        rw [hRow]
        norm_num
    · have hwNotTri : w ∉ triangularLightNeighbors q T G v := fun h => hwLight (Finset.mem_filter.mp h).2.1
      rw [ite_eq_right hwNotTri, zero_add]
      by_cases hLow : 0 < signedDeficiency q G w
      · have hwNonlight : w ∈ nonlightLowVertices q T G := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLow⟩, hwLight⟩
        rw [ite_eq_left hwNonlight]
        apply max_le
        · have hPositive : positiveDeficiency q G w = signedDeficiency q G w := max_eq_left (by omega)
          rw [hPositive, hRow]
          omega
        · exact positiveDeficiency_nonnegative q G w
      · have hwNonlight : w ∉ nonlightLowVertices q T G := by
          intro h
          exact hLow (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
        rw [ite_eq_right hwNonlight]
        rw [hRow]
        omega
  have hSum := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib, neighbor_indicator_weight_sum] at hSum
  have hSubset : triangularLightNeighbors q T G v ⊆ G.neighborFinset v := Finset.filter_subset _ _
  rw [Finset.inter_eq_right.mpr hSubset, one_mul] at hSum
  have hFilter : ((G.neighborFinset v).filter fun w => w ∈ nonlightLowVertices q T G) =
      G.neighborFinset v ∩ nonlightLowVertices q T G := by
    ext w
    simp
  rw [← Finset.sum_filter, hFilter] at hSum
  rw [regular_negativeResidualMass_eq_neighbor_sum q G hFree v hRegular]
  exact hSum

/-- Regular rows with no hub neighbor have a uniform positive-row bound. -/
theorem regular_positivePartners_card_bound (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hIndependent : ∀ l ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj l w)
    (K : ℤ) (hK : 0 ≤ K)
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (v : Fin (q ^ 2 + q + 2)) (hRegular : signedDeficiency q G v = 0)
    (hNoHub : ∀ w ∈ G.neighborFinset v, w ∉ lowHubs q T G)
    (B : ℤ) (hNonlight : ((G.neighborFinset v ∩ nonlightLowVertices q T G).card : ℤ) ≤ B) :
    ((positivePartners q G v).card : ℤ) ≤ 1 + (lightTriangleRegularVertices q T G).card +
      (highVertices q G).card + (K + 1) * B := by
  have hEach (w) (hw : w ∈ G.neighborFinset v ∩ nonlightLowVertices q T G) : positiveDeficiency q G w ≤ K := by
    apply max_le
    · exact hOutside w (hNoHub w (Finset.mem_inter.mp hw).1)
    · exact hK
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  have hTriangles : ((triangularLightNeighbors q T G v).card : ℤ) ≤
      (lightTriangleRegularVertices q T G).card + (highVertices q G).card +
        (G.neighborFinset v ∩ nonlightLowVertices q T G).card := by
    exact_mod_cast triangular_light_neighbor_card_le q T G hFree hIndependent v
  have hMass := regular_negativeResidualMass_le q T G hFree v hRegular
  have hCard := positivePartners_card_le_mass q G v
  rw [positiveResidualMass_balance] at hCard
  have hScaled := mul_le_mul_of_nonneg_left hNonlight (show 0 ≤ K + 1 by omega)
  nlinarith only [hSum, hTriangles, hMass, hCard, hScaled]

/-- Sparse exceptional columns leave only a bounded number of rows with fewer than half good entries. -/
theorem sparse_columns_bad_rows_card_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Finset ι) (Y : Finset κ) (Good : ι → κ → Prop) (E : ℕ)
    (hColumns : ∀ y ∈ Y, (X.filter fun x => ¬Good x y).card ≤ E) :
    (X.filter fun x => 2 * (Y.filter (Good x)).card < Y.card).card ≤ 2 * E := by
  let U := X.filter fun x => 2 * (Y.filter (Good x)).card < Y.card
  let N := fun x => Y.filter fun y => ¬Good x y
  have hN (x) (_hx : x ∈ U) : N x ⊆ Y := Finset.filter_subset _ _
  have hIncidence := finite_family_incidence_eq U Y N hN
  have hColumn (y) (hy : y ∈ Y) : ((U.filter fun x => y ∈ N x).card : ℤ) ≤ E := by
    have hSubset : (U.filter fun x => y ∈ N x) ⊆ X.filter (fun x => ¬Good x y) := by
      intro x hx
      obtain ⟨hxU, hBad⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxU).1, (Finset.mem_filter.mp hBad).2⟩
    exact_mod_cast (Finset.card_le_card hSubset).trans (hColumns y hy)
  have hUpper := Finset.sum_le_sum hColumn
  rw [hIncidence] at hUpper
  simp only [Finset.sum_const, nsmul_eq_mul] at hUpper
  have hRow (x) (hx : x ∈ U) : (Y.card : ℤ) ≤ 2 * (N x).card := by
    have hBad := (Finset.mem_filter.mp hx).2
    have hPartition := Finset.card_filter_add_card_filter_not (s := Y) (p := Good x)
    dsimp only [N]
    omega
  have hLower := Finset.sum_le_sum hRow
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hLower
  by_cases hY : Y.card = 0
  · have hEmpty : U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      omega
    change U.card ≤ _
    simp [hEmpty]
  · have hYPos : (0 : ℤ) < Y.card := by exact_mod_cast (show 0 < Y.card by omega)
    have hProduct : (U.card : ℤ) * Y.card ≤ (2 * (E : ℤ)) * Y.card := by nlinarith only [hLower, hUpper]
    have hBound := (mul_le_mul_iff_of_pos_right hYPos).mp hProduct
    change U.card ≤ _
    exact_mod_cast hBound

/-- A finite cover bounds a set by the sum of the restricted cover sizes. -/
theorem finite_cover_card_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (Y : Finset κ) (N : ι → Finset κ)
    (hCover : ∀ y ∈ Y, ∃ z ∈ P, y ∈ N z) :
    Y.card ≤ ∑ z ∈ P, (Y ∩ N z).card := by
  have hSubset : Y ⊆ P.biUnion (fun z => Y ∩ N z) := by
    intro y hy
    obtain ⟨z, hzP, hyN⟩ := hCover y hy
    exact Finset.mem_biUnion.mpr ⟨z, hzP, Finset.mem_inter.mpr ⟨hy, hyN⟩⟩
  exact (Finset.card_le_card hSubset).trans Finset.card_biUnion_le

theorem closed_neighbor_inter_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (Y : Finset (Fin n)) (z : Fin n) :
    (Y ∩ insert z (G.neighborFinset z)).card ≤ (G.neighborFinset z ∩ Y).card + 1 := by
  have hSubset : Y ∩ insert z (G.neighborFinset z) ⊆ insert z (G.neighborFinset z ∩ Y) := by
    intro y hy
    obtain ⟨hyY, hyClosed⟩ := Finset.mem_inter.mp hy
    rcases Finset.mem_insert.mp hyClosed with hEq | hyN
    · exact Finset.mem_insert.mpr (Or.inl hEq)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mpr ⟨hyN, hyY⟩))
  exact (Finset.card_le_card hSubset).trans (Finset.card_insert_le _ _)

/-- A small closed-neighborhood cover of a large set contains a center meeting many points. -/
theorem closed_cover_large_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (P Y : Finset (Fin n)) (B A : ℕ) (hP : P.card ≤ B) (hY : B * (A + 1) < Y.card)
    (hCover : ∀ y ∈ Y, ∃ z ∈ P, y ∈ insert z (G.neighborFinset z)) :
    ∃ z ∈ P, A < (G.neighborFinset z ∩ Y).card := by
  by_contra h
  push Not at h
  have hCount := finite_cover_card_le P Y (fun z => insert z (G.neighborFinset z)) hCover
  have hEach (z) (hz : z ∈ P) : (Y ∩ insert z (G.neighborFinset z)).card ≤ A + 1 := by
    exact (closed_neighbor_inter_card_le G Y z).trans (by have hBound := h z hz; omega)
  have hSum := Finset.sum_le_sum hEach
  simp at hSum
  have hScaled := Nat.mul_le_mul_right (A + 1) hP
  omega

theorem closed_neighbor_overlap_card_le_two {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (Y : Finset (Fin n)) (z w : Fin n)
    (hY : Y ⊆ G.neighborFinset z) (hzw : z ≠ w) :
    (Y ∩ insert w (G.neighborFinset w)).card ≤ 2 := by
  have hSubset : G.neighborFinset w ∩ Y ⊆ G.neighborFinset z ∩ G.neighborFinset w := by
    intro y hy
    obtain ⟨hyW, hyY⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_inter.mpr ⟨hY hyY, hyW⟩
  have hCount := (Finset.card_le_card hSubset).trans (codegree_le_one G hFree z w hzw)
  have hClosed := closed_neighbor_inter_card_le G Y w
  omega

/-- Covering half of a large neighborhood with boundedly many closed neighborhoods forces its center into the cover. -/
theorem closed_cover_forces_center {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P W S : Finset (Fin n)) (z : Fin n) (B : ℕ)
    (hP : P.card ≤ B) (hW : W ⊆ G.neighborFinset z) (hS : S ⊆ W)
    (hLarge : 4 * B < W.card) (hHalf : W.card ≤ 2 * S.card)
    (hCover : ∀ y ∈ S, ∃ w ∈ P, y ∈ insert w (G.neighborFinset w)) : z ∈ P := by
  by_contra hz
  have hCount := finite_cover_card_le P S (fun w => insert w (G.neighborFinset w)) hCover
  have hEach (w) (hw : w ∈ P) : (S ∩ insert w (G.neighborFinset w)).card ≤ 2 := by
    have hNe : z ≠ w := fun h => hz (h ▸ hw)
    exact closed_neighbor_overlap_card_le_two G hFree S z w (hS.trans hW) hNe
  have hSum := Finset.sum_le_sum hEach
  simp at hSum
  omega

/-- Sparse column exceptions and uniformly small row covers force a shared cover center. -/
theorem sparse_closed_covers_share_center {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (X Y : Finset (Fin n)) (P : Fin n → Finset (Fin n))
    (Good : Fin n → Fin n → Prop) (B E : ℕ)
    (hP : ∀ x ∈ X, (P x).card ≤ B)
    (hColumns : ∀ y ∈ Y, (X.filter fun x => ¬Good x y).card ≤ E)
    (hCover : ∀ x ∈ X, ∀ y ∈ Y, Good x y → ∃ z ∈ P x, y ∈ insert z (G.neighborFinset z))
    (hX : 2 * E < X.card) (hY : 2 * B * (4 * B + 1) < Y.card) :
    ∃ x₀ ∈ X, ∃ z ∈ P x₀, (X.filter fun x => z ∉ P x).card ≤ 2 * E := by
  let bad := X.filter fun x => 2 * (Y.filter (Good x)).card < Y.card
  have hBad : bad.card ≤ 2 * E := sparse_columns_bad_rows_card_le X Y Good E hColumns
  obtain ⟨x₀, hx₀, hx₀Good⟩ := Finset.exists_mem_notMem_of_card_lt_card (hBad.trans_lt hX)
  have hHalf : Y.card ≤ 2 * (Y.filter (Good x₀)).card := by
    have hNot : ¬2 * (Y.filter (Good x₀)).card < Y.card := fun h => hx₀Good (Finset.mem_filter.mpr ⟨hx₀, h⟩)
    omega
  have hLarge : B * (4 * B + 1) < (Y.filter (Good x₀)).card := by nlinarith only [hHalf, hY]
  obtain ⟨z, hzP, hzMany⟩ := closed_cover_large_neighbor G (P x₀) (Y.filter (Good x₀)) B (4 * B)
    (hP x₀ hx₀) hLarge (fun y hy => hCover x₀ hx₀ y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2)
  let W := G.neighborFinset z ∩ Y
  have hW : W ⊆ G.neighborFinset z := Finset.inter_subset_left
  have hWY : W ⊆ Y := Finset.inter_subset_right
  have hWLarge : 4 * B < W.card := by
    have hSubset : G.neighborFinset z ∩ Y.filter (Good x₀) ⊆ W := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).1, (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).1⟩
    exact hzMany.trans_le (Finset.card_le_card hSubset)
  have hColumnsW (y) (hy : y ∈ W) : (X.filter fun x => ¬Good x y).card ≤ E := hColumns y (hWY hy)
  have hBadW := sparse_columns_bad_rows_card_le X W Good E hColumnsW
  have hSubset : (X.filter fun x => z ∉ P x) ⊆ X.filter (fun x => 2 * (W.filter (Good x)).card < W.card) := by
    intro x hx
    obtain ⟨hxX, hzNot⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hxX, ?_⟩
    by_contra h
    have hHalfW : W.card ≤ 2 * (W.filter (Good x)).card := by omega
    apply hzNot
    exact closed_cover_forces_center G hFree (P x) W (W.filter (Good x)) z B
      (hP x hxX) hW (Finset.filter_subset _ _) hWLarge hHalfW
      (fun y hy => hCover x hxX y (hWY (Finset.mem_filter.mp hy).1) (Finset.mem_filter.mp hy).2)
  exact ⟨x₀, hx₀, z, hzP, (Finset.card_le_card hSubset).trans hBadW⟩

theorem vertex_not_own_positivePartner {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    v ∉ positivePartners q G v := by
  intro h
  have hPositive := (Finset.mem_filter.mp h).2
  rw [weightedResidual_diagonal] at hPositive
  have hProduct := int_mul_pred_nonnegative (signedDeficiency q G v)
  nlinarith only [hPositive, hProduct]

theorem low_neighbor_not_positivePartner {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (x l : Fin n) (hAdj : G.Adj x l) (hLow : 1 ≤ signedDeficiency q G l)
    (hNonhigh : 0 ≤ signedDeficiency q G x) : l ∉ positivePartners q G x := by
  intro h
  have hPositive := (Finset.mem_filter.mp h).2
  rw [weightedResidual_off_diagonal q G x l hAdj.ne, adjMatrix_square_codegree] at hPositive
  simp only [G.adjMatrix_apply, ite_eq_left hAdj, one_mul] at hPositive
  have hCodegree : (0 : ℤ) ≤ codegree G x l := by positivity
  omega

theorem nonadjacent_positivePartner_codegree_zero {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (x z : Fin n) (hP : z ∈ positivePartners q G x) (hNot : ¬G.Adj x z) : codegree G x z = 0 := by
  have hNe : x ≠ z := by intro h; subst z; exact vertex_not_own_positivePartner q G x hP
  have hPositive := (Finset.mem_filter.mp hP).2
  rw [weightedResidual_nonadj q G x z hNe hNot] at hPositive
  omega

/-- A positive commutator entry at a nonhigh column gives a closed-neighborhood cover from the positive row. -/
theorem positive_commutator_closed_cover {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (x y : Fin n) (hNonhigh : 0 ≤ signedDeficiency q G y)
    (hPositive : 1 ≤ (weightedAdjacency q G * weightedResidual q G) x y) :
    ∃ z ∈ positivePartners q G x, y ∈ insert z (G.neighborFinset z) := by
  by_contra hNone
  push Not at hNone
  have hEach (z : Fin n) : weightedResidual q G x z * weightedAdjacency q G z y ≤ 0 := by
    by_cases hZ : 0 < weightedResidual q G x z
    · have hzP : z ∈ positivePartners q G x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZ⟩
      have hzNot := hNone z hzP
      have hNe : z ≠ y := by intro h; subst z; exact hzNot (Finset.mem_insert_self _ _)
      have hNot : ¬G.Adj z y := fun h => hzNot (Finset.mem_insert_of_mem ((G.mem_neighborFinset z y).mpr h))
      rw [weightedAdjacency_nonadj q G z y hNe hNot, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hZ)
        (weightedAdjacency_nonhigh_column_nonnegative q G y hNonhigh z)
  have hSum : (weightedResidual q G * weightedAdjacency q G) x y ≤ 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonpos (fun z _ => hEach z)
  rw [← weightedAdjacency_commutes_residual] at hSum
  omega

theorem sum_indicator_card_of_subset {ι : Type*} [DecidableEq ι] (X S : Finset ι) (hS : S ⊆ X) :
    (∑ x ∈ X, if x ∈ S then (1 : ℕ) else 0) = S.card := by
  rw [← Finset.sum_filter]
  have hSet : (X.filter fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  simp [hSet]

/-- A common positive partner of almost all selected neighbors creates a nonedge with few three-edge walks. -/
theorem shared_positive_partner_walk_bound {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l : Fin n) (X : Finset (Fin n))
    (hX : X ⊆ G.neighborFinset l) (hLow : 1 ≤ signedDeficiency q G l)
    (hNonhigh : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (x₀ z : Fin n) (hx₀ : x₀ ∈ X) (hzP : z ∈ positivePartners q G x₀)
    (b : ℕ) (hBad : (X.filter fun x => z ∉ positivePartners q G x).card ≤ b)
    (hSize : b + 1 < X.card) :
    l ≠ z ∧ ¬G.Adj l z ∧
      threeWalkCount G l z ≤ (G.degree l - X.card) + b + 1 := by
  have hLNot : l ∉ positivePartners q G x₀ := low_neighbor_not_positivePartner q G x₀ l
    ((G.mem_neighborFinset l x₀).mp (hX hx₀)).symm hLow (hNonhigh x₀ hx₀)
  have hNe : l ≠ z := by intro h; exact hLNot (h ▸ hzP)
  let bad := X.filter fun x => z ∉ positivePartners q G x
  let adjacent := X ∩ G.neighborFinset z
  change bad.card ≤ b at hBad
  have hAdjacent : adjacent.card ≤ 1 := by
    have hSubset : adjacent ⊆ G.neighborFinset l ∩ G.neighborFinset z := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hX (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
    exact (Finset.card_le_card hSubset).trans (codegree_le_one G hFree l z hNe)
  have hUnion : (bad ∪ adjacent).card < X.card := by
    have h := Finset.card_union_le bad adjacent
    omega
  obtain ⟨x, hx, hxNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hUnion
  have hxP : z ∈ positivePartners q G x := by
    by_contra h
    exact hxNot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩))
  have hxNotAdj : ¬G.Adj x z := by
    intro h
    exact hxNot (Finset.mem_union_right _ (Finset.mem_inter.mpr
      ⟨hx, (G.mem_neighborFinset z x).mpr h.symm⟩))
  have hxZero := nonadjacent_positivePartner_codegree_zero q G x z hxP hxNotAdj
  have hNot : ¬G.Adj l z := by
    intro h
    exact (codegree_eq_zero_iff G x z).mp hxZero l
      ((G.mem_neighborFinset l x).mp (hX hx)).symm h.symm
  have hCount (x : Fin n) (hx : x ∈ G.neighborFinset l) : codegree G x z ≤ 1 := by
    have hxNe : x ≠ z := by intro h; subst x; exact hNot ((G.mem_neighborFinset l z).mp hx)
    exact codegree_le_one G hFree x z hxNe
  have hEach (x) (hx : x ∈ X) : codegree G x z ≤
      (if x ∈ bad then 1 else 0) + (if x ∈ adjacent then 1 else 0) := by
    have hUpper := hCount x (hX hx)
    by_cases hxBad : x ∈ bad
    · rw [ite_eq_left hxBad]
      split_ifs <;> omega
    · rw [ite_eq_right hxBad, zero_add]
      by_cases hxAdjacent : x ∈ adjacent
      · simpa only [ite_eq_left hxAdjacent] using hUpper
      · have hxPartner : z ∈ positivePartners q G x := by
          by_contra h
          exact hxBad (Finset.mem_filter.mpr ⟨hx, h⟩)
        have hNotAdj : ¬G.Adj x z := fun h => hxAdjacent (Finset.mem_inter.mpr
          ⟨hx, (G.mem_neighborFinset z x).mpr h.symm⟩)
        rw [nonadjacent_positivePartner_codegree_zero q G x z hxPartner hNotAdj, ite_eq_right hxAdjacent]
  have hSum := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib, sum_indicator_card_of_subset X bad (Finset.filter_subset _ _),
    sum_indicator_card_of_subset X adjacent Finset.inter_subset_left] at hSum
  have hRest : (∑ x ∈ G.neighborFinset l \ X, codegree G x z) ≤ (G.neighborFinset l \ X).card := by
    have h := Finset.sum_le_sum (fun (x : Fin n) (hx : x ∈ G.neighborFinset l \ X) =>
      hCount x (Finset.mem_sdiff.mp hx).1)
    simpa using h
  have hSplit := Finset.sum_sdiff (f := fun x => codegree G x z) hX
  have hCards := Finset.card_sdiff_add_card_eq_card hX
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hCards
  refine ⟨hNe, hNot, ?_⟩
  unfold threeWalkCount
  omega

/-- Negative entries at a regular column outside the exceptional set come from nonlight low neighbors. -/
theorem regular_negative_entry_support (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (y w : Fin (q ^ 2 + q + 2)) (hY : signedDeficiency q G y = 0)
    (hNotJ : y ∉ lightTriangleRegularVertices q T G) (hNe : w ≠ y)
    (hNegative : weightedResidual q G w y < 0) :
    w ∈ G.neighborFinset y ∩ nonlightLowVertices q T G := by
  have hAdj : G.Adj w y := by
    by_contra h
    have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree w y hNe h
    omega
  have hEntry := weightedResidual_off_diagonal q G w y hNe
  rw [adjMatrix_square_codegree] at hEntry
  simp only [G.adjMatrix_apply, ite_eq_left hAdj, hY, add_zero, one_mul] at hEntry
  have hCodegree : codegree G w y ≤ 1 := codegree_le_one G hFree w y hNe
  have hLow : 0 < signedDeficiency q G w := by omega
  have hNotLight : w ∉ lightLowVertices q T G := by
    intro hLight
    have hUnit := (Finset.mem_filter.mp hLight).2.1
    have hTriangle : codegree G w y = 1 := by omega
    have hRegular : y ∈ triangularRegularNeighbors q G w := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset w y).mpr hAdj, hY⟩, hTriangle⟩
    exact hNotJ (Finset.mem_biUnion.mpr ⟨w, hLight, hRegular⟩)
  exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hAdj.symm,
    Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLow⟩, hNotLight⟩⟩

/-- Negative entries at a light column come from low neighbors or exceptional regular vertices. -/
theorem light_negative_entry_support (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (y w : Fin (q ^ 2 + q + 2)) (hY : y ∈ lightLowVertices q T G) (hNe : w ≠ y)
    (hNegative : weightedResidual q G w y < 0) :
    w ∈ lowNeighbors q G y ∨ w ∈ lightTriangleRegularVertices q T G := by
  have hAdj : G.Adj w y := by
    by_contra h
    have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree w y hNe h
    omega
  have hUnit := (Finset.mem_filter.mp hY).2.1
  have hEntry := weightedResidual_off_diagonal q G w y hNe
  rw [adjMatrix_square_codegree] at hEntry
  simp only [G.adjMatrix_apply, ite_eq_left hAdj, hUnit, one_mul] at hEntry
  have hCodegree : codegree G w y ≤ 1 := codegree_le_one G hFree w y hNe
  by_cases hLow : 0 < signedDeficiency q G w
  · exact Or.inl (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y w).mpr hAdj.symm, hLow⟩)
  · have hZero : signedDeficiency q G w = 0 := by omega
    have hTriangle : codegree G w y = 1 := by omega
    have hRegular : w ∈ triangularRegularNeighbors q G y := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y w).mpr hAdj.symm, hZero⟩,
        by rw [codegree_symm]; exact hTriangle⟩
    exact Or.inr (Finset.mem_biUnion.mpr ⟨y, hY, hRegular⟩)

/-- Only one selected neighbor of l can meet each vertex of a set excluding l. -/
theorem neighbor_hits_set_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l : Fin n) (X S : Finset (Fin n))
    (hX : X ⊆ G.neighborFinset l) (hNot : l ∉ S) :
    (X.filter fun x => ∃ w ∈ S, G.Adj x w).card ≤ S.card := by
  let H := X.filter fun x => ∃ w ∈ S, G.Adj x w
  have hExists (x) (hx : x ∈ H) : ∃ w ∈ S, G.Adj x w := (Finset.mem_filter.mp hx).2
  let witness := fun x => if hx : x ∈ H then (hExists x hx).choose else l
  have hSpec (x) (hx : x ∈ H) : witness x ∈ S ∧ G.Adj x (witness x) := by
    dsimp only [witness]
    rw [dite_eq_left hx]
    exact (hExists x hx).choose_spec
  apply Finset.card_le_card_of_injOn witness
  · intro x hx
    exact (hSpec x hx).1
  · intro x hx y hy hEq
    have hLX := (G.mem_neighborFinset l x).mp (hX (Finset.mem_filter.mp hx).1)
    have hLY := (G.mem_neighborFinset l y).mp (hX (Finset.mem_filter.mp hy).1)
    have hWX := (hSpec x hx).2.symm
    have hWY := (hSpec y hy).2.symm
    rw [← hEq] at hWY
    have hNe : l ≠ witness x := by intro h; exact hNot (h ▸ (hSpec x hx).1)
    exact common_neighbor_unique G hFree hNe hLX hWX hLY hWY

theorem bad_commutator_has_negative_neighbor {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (x l y : Fin n) (hL : l ∈ G.neighborFinset x) (hEntry : weightedResidual q G l y = 1)
    (hNonhigh : 0 ≤ signedDeficiency q G x) (hNonnegative : 0 ≤ weightedResidual q G x y)
    (hBad : (weightedAdjacency q G * weightedResidual q G) x y < 1) :
    ∃ w ∈ (G.neighborFinset x).erase l, weightedResidual q G w y < 0 := by
  by_contra h
  push Not at h
  have hRest : 0 ≤ ∑ w ∈ (G.neighborFinset x).erase l, weightedResidual q G w y := by
    apply Finset.sum_nonneg
    intro w hw
    have hTerm := h w hw
    omega
  have hSplit := Finset.sum_erase_add (G.neighborFinset x) (fun w => weightedResidual q G w y) hL
  rw [hEntry] at hSplit
  rw [weightedAdjacency_mul_apply] at hBad
  have hLoop := mul_nonneg hNonhigh hNonnegative
  linarith only [hBad, hSplit, hRest, hLoop]

/-- A small negative-support set bounds the exceptional entries in one propagated column. -/
theorem negative_support_column_exceptions (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l y : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (hY : y ∈ positivePartners q G l) (hNonhighY : 0 ≤ signedDeficiency q G y)
    (X S : Finset (Fin (q ^ 2 + q + 2))) (hX : X ⊆ G.neighborFinset l)
    (hNonhighX : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (hNotS : l ∉ S)
    (hSupport : ∀ w, w ≠ y → weightedResidual q G w y < 0 →
      w ∈ S ∨ w ∈ lightTriangleRegularVertices q T G)
    (hAvoid : ∀ x ∈ X, Disjoint (G.neighborFinset x) (lightTriangleRegularVertices q T G)) :
    (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ S.card := by
  obtain ⟨hNe, hNot, hZero⟩ := positivePartner_nonhigh q G l y hLow hNonhighY hY
  have hEntry : weightedResidual q G l y = 1 := by
    rw [weightedResidual_nonadj q G l y hNe hNot, hZero]
    norm_num
  have hSubset : (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1) ⊆
      X.filter (fun x => ∃ w ∈ S, G.Adj x w) := by
    intro x hx
    obtain ⟨hxX, hxBad⟩ := Finset.mem_filter.mp hx
    have hLX := (G.mem_neighborFinset l x).mp (hX hxX)
    have hXYNe : x ≠ y := by intro h; subst x; exact hNot hLX
    have hXYNot : ¬G.Adj x y := by
      intro h
      exact (codegree_eq_zero_iff G l y).mp hZero x hLX h.symm
    have hZXY := weightedResidual_nonadj_nonnegative q G hFree x y hXYNe hXYNot
    obtain ⟨w, hw, hwNegative⟩ := bad_commutator_has_negative_neighbor q G x l y
      ((G.mem_neighborFinset x l).mpr hLX.symm) hEntry (hNonhighX x hxX) hZXY hxBad
    have hXW := (G.mem_neighborFinset x w).mp (Finset.mem_erase.mp hw).2
    have hWYNe : w ≠ y := by intro h; subst w; exact hXYNot hXW
    rcases hSupport w hWYNe hwNegative with hwS | hwJ
    · exact Finset.mem_filter.mpr ⟨hxX, w, hwS, hXW⟩
    · exact False.elim ((Finset.disjoint_left.mp (hAvoid x hxX)) (Finset.mem_erase.mp hw).2 hwJ)
  exact (Finset.card_le_card hSubset).trans (neighbor_hits_set_card_le G hFree l X S hX hNotS)

/-- Bounded positive rows and sparse commutator exceptions force a uniform bound on the propagated set. -/
theorem positive_row_propagation_bound {n : ℕ} (q C B E F : ℕ)
    (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G)
    (l : Fin n) (X Y : Finset (Fin n)) (hX : X ⊆ G.neighborFinset l)
    (hLow : 1 ≤ signedDeficiency q G l) (hNonhighX : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (hNonhighY : ∀ y ∈ Y, 0 ≤ signedDeficiency q G y)
    (hRows : ∀ x ∈ X, (positivePartners q G x).card ≤ B)
    (hExceptions : ∀ y ∈ Y,
      (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ E)
    (hMissing : (G.neighborFinset l \ X).card ≤ F) (hMany : 2 * E + 1 < X.card)
    (hOrder : 8 * C * (F + 2 * E + 1) < q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    Y.card ≤ 2 * B * (4 * B + 1) := by
  classical
  by_contra h
  have hLarge : 2 * B * (4 * B + 1) < Y.card := by omega
  let Good := fun x y => 1 ≤ (weightedAdjacency q G * weightedResidual q G) x y
  have hCover (x) (_hx : x ∈ X) (y) (hy : y ∈ Y) (hGood : Good x y) :
      ∃ z ∈ positivePartners q G x, y ∈ insert z (G.neighborFinset z) :=
    positive_commutator_closed_cover q G x y (hNonhighY y hy) hGood
  obtain ⟨x₀, hx₀, z, hz, hShared⟩ := sparse_closed_covers_share_center G hFree X Y
    (positivePartners q G) Good B E hRows (by
      intro y hy
      refine le_trans (le_of_eq ?_) (hExceptions y hy)
      congr 1
      ext x
      simp only [Finset.mem_filter, Good, not_le]) hCover (by omega) hLarge
  obtain ⟨hNe, hNot, hWalk⟩ := shared_positive_partner_walk_bound q G hFree l X hX hLow hNonhighX
    x₀ z hx₀ hz (2 * E) hShared hMany
  have hCards := Finset.card_sdiff_add_card_eq_card hX
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hCards
  have hWalkBound : threeWalkCount G l z ≤ F + 2 * E + 1 := by omega
  have hUpper := withEdge_copyCount_le G hFree l z hNe
  have hUpperScaled := Nat.mul_le_mul_left C hUpper
  have hWalkScaled := Nat.mul_le_mul_left (8 * C) hWalkBound
  have hLower := hNoCheap l z hNe hNot
  nlinarith only [hUpperScaled, hWalkScaled, hLower, hOrder]

/-- Regular and light positive columns have only boundedly many bad commutator entries among the selected neighbors. -/
theorem regular_or_light_column_exceptions (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l y : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (hY : y ∈ positivePartners q G l)
    (hType : (signedDeficiency q G y = 0 ∧ y ∉ lightTriangleRegularVertices q T G) ∨ y ∈ lightLowVertices q T G)
    (X : Finset (Fin (q ^ 2 + q + 2))) (hX : X ⊆ G.neighborFinset l)
    (hNonhighX : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (hAvoid : ∀ x ∈ X, Disjoint (G.neighborFinset x) (lightTriangleRegularVertices q T G))
    (E : ℕ) (hLightDegree : ∀ v ∈ lightLowVertices q T G, (lowNeighbors q G v).card ≤ E)
    (hNonlightDegree : ∀ v, signedDeficiency q G v = 0 → (G.neighborFinset v ∩ nonlightLowVertices q T G).card ≤ E) :
    (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ E := by
  rcases hType with ⟨hRegular, hNotJ⟩ | hLight
  · have hNonhigh : 0 ≤ signedDeficiency q G y := by omega
    obtain ⟨_, hNot, _⟩ := positivePartner_nonhigh q G l y hLow hNonhigh hY
    have hNotS : l ∉ G.neighborFinset y ∩ nonlightLowVertices q T G := by
      intro h
      exact hNot ((G.mem_neighborFinset y l).mp (Finset.mem_inter.mp h).1).symm
    have hSupport (w) (hNe : w ≠ y) (hNegative : weightedResidual q G w y < 0) :
        w ∈ G.neighborFinset y ∩ nonlightLowVertices q T G ∨ w ∈ lightTriangleRegularVertices q T G :=
      Or.inl (regular_negative_entry_support q T G hFree y w hRegular hNotJ hNe hNegative)
    exact (negative_support_column_exceptions q T G hFree l y hLow hY hNonhigh X
      (G.neighborFinset y ∩ nonlightLowVertices q T G) hX hNonhighX hNotS hSupport hAvoid).trans
      (hNonlightDegree y hRegular)
  · have hUnit := (Finset.mem_filter.mp hLight).2.1
    have hNonhigh : 0 ≤ signedDeficiency q G y := by omega
    obtain ⟨_, hNot, _⟩ := positivePartner_nonhigh q G l y hLow hNonhigh hY
    have hNotS : l ∉ lowNeighbors q G y := by
      intro h
      exact hNot ((G.mem_neighborFinset y l).mp (Finset.mem_filter.mp h).1).symm
    have hSupport (w) (hNe : w ≠ y) (hNegative : weightedResidual q G w y < 0) :
        w ∈ lowNeighbors q G y ∨ w ∈ lightTriangleRegularVertices q T G :=
      light_negative_entry_support q T G hFree y w hLight hNe hNegative
    exact (negative_support_column_exceptions q T G hFree l y hLow hY hNonhigh X
      (lowNeighbors q G y) hX hNonhighX hNotS hSupport hAvoid).trans (hLightDegree y hLight)

def goodPositivePartners {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  ((positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ lightLowVertices q T G) \
    lightTriangleRegularVertices q T G

/-- The propagated regular and light part of every low positive row is bounded by explicit finite constants. -/
theorem good_positivePartners_card_le (q C T B E F : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (X : Finset (Fin (q ^ 2 + q + 2))) (hX : X ⊆ G.neighborFinset l)
    (hNonhighX : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (hAvoid : ∀ x ∈ X, Disjoint (G.neighborFinset x) (lightTriangleRegularVertices q T G))
    (hRows : ∀ x ∈ X, (positivePartners q G x).card ≤ B)
    (hLightDegree : ∀ v ∈ lightLowVertices q T G, (lowNeighbors q G v).card ≤ E)
    (hNonlightDegree : ∀ v, signedDeficiency q G v = 0 → (G.neighborFinset v ∩ nonlightLowVertices q T G).card ≤ E)
    (hMissing : (G.neighborFinset l \ X).card ≤ F) (hMany : 2 * E + 1 < X.card)
    (hOrder : 8 * C * (F + 2 * E + 1) < q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    (((positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ lightLowVertices q T G).card : ℕ) ≤
      2 * B * (4 * B + 1) + (lightTriangleRegularVertices q T G).card := by
  let Y := goodPositivePartners q T G l
  have hSpec (y) (hy : y ∈ Y) : y ∈ positivePartners q G l ∧
      ((signedDeficiency q G y = 0 ∧ y ∉ lightTriangleRegularVertices q T G) ∨ y ∈ lightLowVertices q T G) := by
    obtain ⟨hyFilter, hyNot⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hyP, hyType⟩ := Finset.mem_filter.mp hyFilter
    refine ⟨hyP, ?_⟩
    rcases hyType with hRegular | hLight
    · exact Or.inl ⟨hRegular, hyNot⟩
    · exact Or.inr hLight
  have hNonhighY (y) (hy : y ∈ Y) : 0 ≤ signedDeficiency q G y := by
    rcases (hSpec y hy).2 with ⟨hRegular, _⟩ | hLight
    · omega
    · have hUnit := (Finset.mem_filter.mp hLight).2.1
      omega
  have hExceptions (y) (hy : y ∈ Y) :
      (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ E :=
    regular_or_light_column_exceptions q T G hFree l y hLow (hSpec y hy).1 (hSpec y hy).2
      X hX hNonhighX hAvoid E hLightDegree hNonlightDegree
  have hBound := positive_row_propagation_bound q C B E F G hFree l X Y hX hLow hNonhighX hNonhighY
    hRows hExceptions hMissing hMany hOrder hNoCheap
  have hCard := Finset.card_le_card_sdiff_add_card
    (s := (positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ lightLowVertices q T G)
    (t := lightTriangleRegularVertices q T G)
  change _ ≤ Y.card + _ at hCard
  omega

def propagationNeighbors {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  ((G.neighborFinset l).filter fun x => signedDeficiency q G x = 0 ∨ x ∈ lightLowVertices q T G).filter fun x =>
    Disjoint (G.neighborFinset x) (lightTriangleRegularVertices q T G) ∧
      Disjoint (G.neighborFinset x) (lowHubs q T G)

theorem propagationNeighbors_mem {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (l x : Fin n) :
    x ∈ propagationNeighbors q T G l ↔ x ∈ G.neighborFinset l ∧
      (signedDeficiency q G x = 0 ∨ x ∈ lightLowVertices q T G) ∧
      Disjoint (G.neighborFinset x) (lightTriangleRegularVertices q T G) ∧
      Disjoint (G.neighborFinset x) (lowHubs q T G) := by
  simp only [propagationNeighbors, Finset.mem_filter, and_assoc]

/-- Only boundedly many neighbors fail the type and avoidance conditions for propagation. -/
theorem propagationNeighbors_missing_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l) (hNotHub : l ∉ lowHubs q T G)
    (M : ℕ) (hNonlight : (G.neighborFinset l ∩ nonlightLowVertices q T G).card ≤ M) :
    (G.neighborFinset l \ propagationNeighbors q T G l).card ≤ M + (highVertices q G).card +
      (lightTriangleRegularVertices q T G).card + (lowHubs q T G).card := by
  let N := G.neighborFinset l
  let badType := N.filter fun x => ¬(signedDeficiency q G x = 0 ∨ x ∈ lightLowVertices q T G)
  let hitJ := N.filter fun x => ∃ w ∈ lightTriangleRegularVertices q T G, G.Adj x w
  let hitU := N.filter fun x => ∃ w ∈ lowHubs q T G, G.Adj x w
  have hBadCover : badType ⊆ (N ∩ nonlightLowVertices q T G) ∪ highVertices q G := by
    intro x hx
    obtain ⟨hxN, hxBad⟩ := Finset.mem_filter.mp hx
    have hxNotZero : signedDeficiency q G x ≠ 0 := fun h => hxBad (Or.inl h)
    have hxNotLight : x ∉ lightLowVertices q T G := fun h => hxBad (Or.inr h)
    by_cases hPositive : 0 < signedDeficiency q G x
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxN,
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPositive⟩, hxNotLight⟩⟩)
    · exact Finset.mem_union_right _ ((mem_highVertices_iff q G x).mpr (by omega))
  have hBadCard : badType.card ≤ M + (highVertices q G).card := by
    have h := (Finset.card_le_card hBadCover).trans (Finset.card_union_le _ _)
    change (N ∩ nonlightLowVertices q T G).card ≤ M at hNonlight
    omega
  have hNotJ : l ∉ lightTriangleRegularVertices q T G := by
    intro h
    have hZero := lightTriangleRegularVertices_regular q T G l h
    omega
  have hJCard : hitJ.card ≤ (lightTriangleRegularVertices q T G).card :=
    neighbor_hits_set_card_le G hFree l N _ (fun _ h => h) hNotJ
  have hUCard : hitU.card ≤ (lowHubs q T G).card :=
    neighbor_hits_set_card_le G hFree l N _ (fun _ h => h) hNotHub
  have hCover : N \ propagationNeighbors q T G l ⊆ badType ∪ hitJ ∪ hitU := by
    intro x hx
    obtain ⟨hxN, hxNot⟩ := Finset.mem_sdiff.mp hx
    by_cases hType : signedDeficiency q G x = 0 ∨ x ∈ lightLowVertices q T G
    · by_cases hJ : Disjoint (G.neighborFinset x) (lightTriangleRegularVertices q T G)
      · by_cases hU : Disjoint (G.neighborFinset x) (lowHubs q T G)
        · exact False.elim (hxNot ((propagationNeighbors_mem q T G l x).mpr ⟨hxN, hType, hJ, hU⟩))
        · obtain ⟨w, hwN, hwU⟩ := Finset.not_disjoint_iff.mp hU
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxN, w, hwU, (G.mem_neighborFinset x w).mp hwN⟩)
      · obtain ⟨w, hwN, hwJ⟩ := Finset.not_disjoint_iff.mp hJ
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hxN, w, hwJ, (G.mem_neighborFinset x w).mp hwN⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxN, hType⟩))
  have hTotal := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hFirst := Finset.card_union_le badType hitJ
  change (N \ propagationNeighbors q T G l).card ≤ _
  omega

/-- Both kinds of selected propagation neighbors have uniformly bounded positive rows. -/
theorem propagationNeighbors_positive_card_le (q T K M : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (hIndependent : ∀ v ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj v w)
    (hTriangles : ∀ w ∈ lightLowVertices q T G, (triangularRegularNeighbors q G w).card ≤ 16)
    (hNonlight : ∀ w, w ∉ lowHubs q T G → (G.neighborFinset w ∩ nonlightLowVertices q T G).card ≤ M)
    (l x : Fin (q ^ 2 + q + 2)) (hx : x ∈ propagationNeighbors q T G l) :
    (positivePartners q G x).card ≤ 17 + (lightTriangleRegularVertices q T G).card +
      (highVertices q G).card + (K + 1) * M := by
  obtain ⟨_, hType, _, hAvoidHub⟩ := (propagationNeighbors_mem q T G l x).mp hx
  rcases hType with hRegular | hLight
  · have hNotHub : x ∉ lowHubs q T G := by
      intro h
      have hPositive := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
      omega
    have hRow := regular_positivePartners_card_bound q T G hFree hIndependent K (Nat.cast_nonneg K) hOutside x hRegular
      (fun w hw h => (Finset.disjoint_left.mp hAvoidHub) hw h) M
      (by exact_mod_cast hNonlight x hNotHub)
    have hRowNat : (positivePartners q G x).card ≤ 1 + (lightTriangleRegularVertices q T G).card +
        (highVertices q G).card + (K + 1) * M := by exact_mod_cast hRow
    omega
  · obtain ⟨hxOutside, hUnit, _⟩ := Finset.mem_filter.mp hLight
    obtain ⟨hxLow, hxNotClosure⟩ := Finset.mem_sdiff.mp hxOutside
    have hxNotHub : x ∉ lowHubs q T G := fun h => hxNotClosure (Finset.mem_union_left _ h)
    have hWeight := (outside_lowHubClosure_bounds q T K G hOutside x hxLow hxNotClosure).2.1
    have hRow := unit_positivePartners_card_le q G hFree x hUnit (hTriangles x hLight) K hWeight
    have hDegree : (lowNeighbors q G x).card ≤ M := by
      rw [light_lowNeighbors_eq_nonlight q T G hIndependent x hLight]
      exact hNonlight x hxNotHub
    have hDegreeInt : ((lowNeighbors q G x).card : ℤ) ≤ M := by exact_mod_cast hDegree
    have hScaled := mul_le_mul_of_nonneg_left hDegreeInt (show (0 : ℤ) ≤ K + 1 by positivity)
    have hRowNat : (positivePartners q G x).card ≤ 17 + (highVertices q G).card + (K + 1) * M := by
      have hFinal : ((positivePartners q G x).card : ℤ) ≤ 17 + (highVertices q G).card + ((K : ℤ) + 1) * M := by
        nlinarith only [hRow, hScaled]
      exact_mod_cast hFinal
    omega

/-- Explicit finite form of the positive-row propagation bound outside the low hubs. -/
theorem low_positive_regular_light_bound (q C T K M : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (hIndependent : ∀ v ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj v w)
    (hTriangles : ∀ w ∈ lightLowVertices q T G, (triangularRegularNeighbors q G w).card ≤ 16)
    (hNonlight : ∀ w, w ∉ lowHubs q T G → (G.neighborFinset w ∩ nonlightLowVertices q T G).card ≤ M)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l) (hNotHub : l ∉ lowHubs q T G)
    (hCount : K + (M + (highVertices q G).card + (lightTriangleRegularVertices q T G).card +
      (lowHubs q T G).card) + 2 * M + 1 ≤ q)
    (hOrder : 8 * C * (M + (highVertices q G).card + (lightTriangleRegularVertices q T G).card +
      (lowHubs q T G).card + 2 * M + 1) < q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    let B := 17 + (lightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M
    (((positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ lightLowVertices q T G).card : ℕ) ≤
      2 * B * (4 * B + 1) + (lightTriangleRegularVertices q T G).card := by
  let X := propagationNeighbors q T G l
  let F := M + (highVertices q G).card + (lightTriangleRegularVertices q T G).card + (lowHubs q T G).card
  let B := 17 + (lightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M
  have hX : X ⊆ G.neighborFinset l := fun x hx => ((propagationNeighbors_mem q T G l x).mp hx).1
  have hNonhighX (x) (hx : x ∈ X) : 0 ≤ signedDeficiency q G x := by
    rcases ((propagationNeighbors_mem q T G l x).mp hx).2.1 with hRegular | hLight
    · omega
    · have hUnit := (Finset.mem_filter.mp hLight).2.1
      omega
  have hAvoid (x) (hx : x ∈ X) : Disjoint (G.neighborFinset x) (lightTriangleRegularVertices q T G) :=
    ((propagationNeighbors_mem q T G l x).mp hx).2.2.1
  have hRows (x) (hx : x ∈ X) : (positivePartners q G x).card ≤ B :=
    propagationNeighbors_positive_card_le q T K M G hFree hOutside hIndependent hTriangles hNonlight l x hx
  have hLightDegree (w) (hw : w ∈ lightLowVertices q T G) : (lowNeighbors q G w).card ≤ M := by
    have hNotClosure := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
    have hNot : w ∉ lowHubs q T G := fun h => hNotClosure (Finset.mem_union_left _ h)
    rw [light_lowNeighbors_eq_nonlight q T G hIndependent w hw]
    exact hNonlight w hNot
  have hNonlightDegree (w) (hw : signedDeficiency q G w = 0) :
      (G.neighborFinset w ∩ nonlightLowVertices q T G).card ≤ M := by
    apply hNonlight w
    intro h
    have hPositive := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
    omega
  have hMissing : (G.neighborFinset l \ X).card ≤ F :=
    propagationNeighbors_missing_card_le q T G hFree l hLow hNotHub M (hNonlight l hNotHub)
  have hDegree : q + 1 ≤ G.degree l + K := by
    have hBound := hOutside l hNotHub
    unfold signedDeficiency at hBound
    omega
  have hPartition := Finset.card_sdiff_add_card_eq_card hX
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hPartition
  have hMany : 2 * M + 1 < X.card := by
    change K + F + 2 * M + 1 ≤ q at hCount
    omega
  have hOrderF : 8 * C * (F + 2 * M + 1) < q := hOrder
  exact good_positivePartners_card_le q C T B M F G hFree l hLow X hX hNonhighX hAvoid hRows
    hLightDegree hNonlightDegree hMissing hMany hOrderF hNoCheap

def regularPartnersOutsideTriangles {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) : Finset (Fin n) :=
  regularPositivePartners q G u \ lightTriangleRegularVertices q T G

/-- A large-deficiency vertex has a large regular positive row outside the exceptional set. -/
theorem regularPartnersOutsideTriangles_card_lower (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (u : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G u) :
    (signedDeficiency q G u - 3) * q - 3 * (highVertices q G).card -
      (lightTriangleRegularVertices q T G).card ≤ ((regularPartnersOutsideTriangles q T G u).card : ℤ) := by
  have hRow := (regular_positivePartners_card_bounds q G hFree hDegree u hLow).1
  have hLowCount := lowPositivePartners_card_le_total q G u
  have hTotal := dense_positiveDeficiency_le_high_card q G hDegree hDense
  have hWeight : 0 ≤ ∑ w ∈ G.neighborFinset u, positiveDeficiency q G w :=
    Finset.sum_nonneg (fun w _ => positiveDeficiency_nonnegative q G w)
  have hTriangle : (0 : ℤ) ≤ (triangularNeighbors G u).card := by positivity
  have hRemoval : ((regularPositivePartners q G u).card : ℤ) ≤
      (regularPartnersOutsideTriangles q T G u).card + (lightTriangleRegularVertices q T G).card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card
      (s := regularPositivePartners q G u) (t := lightTriangleRegularVertices q T G))
  nlinarith only [hRow, hLowCount, hTotal, hWeight, hTriangle, hRemoval, hLow]

/-- At a neighbor of u, only the neighborhoods of its nonlight low neighbors can cause bad regular columns. -/
theorem regular_partner_bad_columns_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (u x : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G u)
    (hUX : G.Adj u x) (hNonhigh : 0 ≤ signedDeficiency q G x)
    (M : ℕ) (hNonlight : (G.neighborFinset x ∩ nonlightLowVertices q T G).card ≤ M) :
    ((regularPartnersOutsideTriangles q T G u).filter fun y =>
      (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ M * (q + 2) := by
  let Y := regularPartnersOutsideTriangles q T G u
  let N := G.neighborFinset x ∩ nonlightLowVertices q T G
  have hCover : (Y.filter fun y => (weightedAdjacency q G * weightedResidual q G) x y < 1) ⊆
      N.biUnion (fun w => G.neighborFinset w) := by
    intro y hy
    obtain ⟨hyY, hyBad⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyP, hyNotJ⟩ := Finset.mem_sdiff.mp hyY
    obtain ⟨hyPositive, hyRegular⟩ := Finset.mem_filter.mp hyP
    obtain ⟨hUY, hUYNot, hZero⟩ := positivePartner_nonhigh q G u y hLow (by omega) hyPositive
    have hEntry : weightedResidual q G u y = 1 := by
      rw [weightedResidual_nonadj q G u y hUY hUYNot, hZero]
      norm_num
    have hXYNe : x ≠ y := by intro h; subst x; exact hUYNot hUX
    have hXYNot : ¬G.Adj x y := by
      intro h
      exact (codegree_eq_zero_iff G u y).mp hZero x hUX h.symm
    have hNonneg := weightedResidual_nonadj_nonnegative q G hFree x y hXYNe hXYNot
    obtain ⟨w, hw, hwNegative⟩ := bad_commutator_has_negative_neighbor q G x u y
      ((G.mem_neighborFinset x u).mpr hUX.symm) hEntry hNonhigh hNonneg hyBad
    have hXW := (G.mem_neighborFinset x w).mp (Finset.mem_erase.mp hw).2
    have hWY : w ≠ y := by intro h; subst w; exact hXYNot hXW
    have hSupport := regular_negative_entry_support q T G hFree y w hyRegular hyNotJ hWY hwNegative
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_inter.mpr
      ⟨(Finset.mem_erase.mp hw).2, (Finset.mem_inter.mp hSupport).2⟩,
      (G.mem_neighborFinset w y).mpr ((G.mem_neighborFinset y w).mp (Finset.mem_inter.mp hSupport).1).symm⟩
  have hUnion : (N.biUnion (fun w => G.neighborFinset w)).card ≤ N.card * (q + 2) := by
    calc
      _ ≤ ∑ w ∈ N, (G.neighborFinset w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ N, (q + 2) := by
        apply Finset.sum_le_sum
        intro w _
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hDegree w
      _ = _ := by simp
  have hScale := Nat.mul_le_mul_right (q + 2) hNonlight
  exact (Finset.card_le_card hCover).trans (hUnion.trans hScale)

/-- The no-cheap-edge gap bounds every closed-neighborhood cover of nonhigh positive partners. -/
theorem positive_closed_cover_scaled_bound (q C : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (u : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G u) (Y P : Finset (Fin (q ^ 2 + q + 2)))
    (hY : Y ⊆ positivePartners q G u) (hNonhigh : ∀ y ∈ Y, 0 ≤ signedDeficiency q G y)
    (hCover : ∀ y ∈ Y, ∃ z ∈ P, y ∈ insert z (G.neighborFinset z))
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    (8 * (C : ℤ)) * Y.card ≤ P.card * ((8 * C - 1) * (q : ℤ) + 24 * C) := by
  let L : ℤ := 8 * C
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hEach (z) (_hz : z ∈ P) : L * (Y ∩ insert z (G.neighborFinset z)).card ≤
      (L - 1) * (q : ℤ) + 3 * L := by
    have hClosed := closed_neighbor_inter_card_le G Y z
    have hClosedInt : ((Y ∩ insert z (G.neighborFinset z)).card : ℤ) ≤
        (G.neighborFinset z ∩ Y).card + 1 := by exact_mod_cast hClosed
    have hScaled := mul_le_mul_of_nonneg_left hClosedInt (show 0 ≤ L by omega)
    by_cases hEmpty : (G.neighborFinset z ∩ Y).card = 0
    · rw [hEmpty, Nat.cast_zero] at hScaled
      have hTerm : 0 ≤ (L - 1) * (q : ℤ) := by positivity
      nlinarith only [hScaled, hTerm, hL]
    · have hGap : (q : ℤ) + L * (G.neighborFinset z ∩ Y).card ≤ L * G.degree z := by
        dsimp [L]
        exact_mod_cast no_cheap_edge_block_degree_gap q C G hFree u z hLow Y hY hNonhigh (by omega) hNoCheap
      have hDegreeInt : (G.degree z : ℤ) ≤ (q : ℤ) + 2 := by exact_mod_cast hDegree z
      have hDegreeScaled := mul_le_mul_of_nonneg_left hDegreeInt (show 0 ≤ L by omega)
      nlinarith only [hScaled, hGap, hDegreeScaled]
  have hCount : (Y.card : ℤ) ≤ ∑ z ∈ P, ((Y ∩ insert z (G.neighborFinset z)).card : ℤ) := by
    exact_mod_cast finite_cover_card_le P Y (fun z => insert z (G.neighborFinset z)) hCover
  have hCountScaled := mul_le_mul_of_nonneg_left hCount (show 0 ≤ L by omega)
  have hSum := Finset.sum_le_sum hEach
  simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hSum
  have hBound := hCountScaled.trans hSum
  dsimp only [L] at hBound
  nlinarith only [hBound]

/-- The large-row comparison forces a bounded deficiency when a neighboring positive row is small. -/
theorem growing_neighbor_numeric_bound (q k L M B R : ℤ)
    (hq : 1 ≤ q) (hL : 1 ≤ L) (hSix : 6 * L ≤ q) (hk : 0 ≤ k)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hCompare : L * ((k - 3 - M) * q - R - 2 * M) ≤
      (k + B) * ((L - 1) * q + 3 * L)) :
    k ≤ 2 * L * (3 * M + 4 * B + R + 3) := by
  have hMain : k * (q - 3 * L) ≤ L * (M + 3) * q + B * (L - 1) * q + L * (R + 2 * M + 3 * B) := by
    linear_combination hCompare
  have hKScale := mul_le_mul_of_nonneg_left hSix hk
  have hRest := mul_nonneg (show 0 ≤ L * (R + 2 * M + 3 * B) by positivity) (show 0 ≤ q - 1 by omega)
  have hBExtra := mul_nonneg hB (show 0 ≤ q by omega)
  have hFinal : q * k ≤ q * (2 * L * (3 * M + 4 * B + R + 3)) := by
    nlinarith only [hMain, hKScale, hRest, hBExtra]
  exact (mul_le_mul_iff_of_pos_left (show 0 < q by omega)).mp hFinal

/-- A neighboring row of size k plus a constant bounds the root deficiency k. -/
theorem small_neighbor_row_comparison (q C T M B : ℕ) (hC : 1 ≤ C)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (u x : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G u)
    (hUX : G.Adj u x) (hNonhigh : 0 ≤ signedDeficiency q G x)
    (hNonlight : (G.neighborFinset x ∩ nonlightLowVertices q T G).card ≤ M)
    (hRow : ((positivePartners q G x).card : ℤ) ≤ signedDeficiency q G u + B)
    (hNoCheap : ∀ v w (hvw : v ≠ w), ¬G.Adj v w →
      q ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4)) :
    (8 * (C : ℤ)) * ((signedDeficiency q G u - 3 - M) * q -
      (3 * (highVertices q G).card + (lightTriangleRegularVertices q T G).card) - 2 * M) ≤
      (signedDeficiency q G u + B) * (((8 * (C : ℤ)) - 1) * q + 3 * (8 * (C : ℤ))) := by
  let k := signedDeficiency q G u
  let L : ℤ := 8 * C
  let R : ℤ := 3 * (highVertices q G).card + (lightTriangleRegularVertices q T G).card
  let Y := regularPartnersOutsideTriangles q T G u
  let bad := Y.filter fun y => (weightedAdjacency q G * weightedResidual q G) x y < 1
  let S := Y \ bad
  have hYPositive : Y ⊆ positivePartners q G u := by
    intro y hy
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).1
  have hYRegular (y) (hy : y ∈ Y) : signedDeficiency q G y = 0 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).2
  have hSPositive : S ⊆ positivePartners q G u := fun _ hy => hYPositive (Finset.mem_sdiff.mp hy).1
  have hSNonhigh (y) (hy : y ∈ S) : 0 ≤ signedDeficiency q G y := by
    rw [hYRegular y (Finset.mem_sdiff.mp hy).1]
  have hCover (y) (hy : y ∈ S) : ∃ z ∈ positivePartners q G x, y ∈ insert z (G.neighborFinset z) := by
    obtain ⟨hyY, hyNot⟩ := Finset.mem_sdiff.mp hy
    have hGood : 1 ≤ (weightedAdjacency q G * weightedResidual q G) x y := by
      by_contra h
      exact hyNot (Finset.mem_filter.mpr ⟨hyY, by omega⟩)
    exact positive_commutator_closed_cover q G x y (hSNonhigh y hy) hGood
  have hCoverBound := positive_closed_cover_scaled_bound q C hC G hFree hDegree u hLow S
    (positivePartners q G x) hSPositive hSNonhigh hCover hNoCheap
  have hBad := regular_partner_bad_columns_card_le q T G hFree hDegree u x hLow hUX hNonhigh M hNonlight
  have hPartition := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset
    (fun y => (weightedAdjacency q G * weightedResidual q G) x y < 1) Y)
  change S.card + bad.card = Y.card at hPartition
  have hPartitionInt : (S.card : ℤ) + bad.card = Y.card := by exact_mod_cast hPartition
  have hBadInt : (bad.card : ℤ) ≤ (M : ℤ) * ((q : ℤ) + 2) := by exact_mod_cast hBad
  have hLowerRaw := regularPartnersOutsideTriangles_card_lower q T G hFree hDegree hDense u hLow
  have hLower : (k - 3) * q - R ≤ (Y.card : ℤ) := by
    dsimp [k, R, Y]
    nlinarith only [hLowerRaw]
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hLowerS : (k - 3 - M) * (q : ℤ) - R - 2 * M ≤ S.card := by
    nlinarith only [hPartitionInt, hBadInt, hLower]
  have hLowerScaled := mul_le_mul_of_nonneg_left hLowerS (show 0 ≤ L by omega)
  have hQ : 0 ≤ (L - 1) * (q : ℤ) + 3 * L := by
    exact add_nonneg (mul_nonneg (by omega) (Nat.cast_nonneg q)) (by omega)
  have hRowScaled := mul_le_mul_of_nonneg_right hRow hQ
  have hComparison : L * ((k - 3 - M) * (q : ℤ) - R - 2 * M) ≤
      (k + B) * ((L - 1) * (q : ℤ) + 3 * L) := by
    dsimp only [L] at hLowerScaled hRowScaled
    nlinarith only [hLowerScaled, hCoverBound, hRowScaled]
  exact hComparison

theorem small_neighbor_row_bounds_deficiency (q C T M B : ℕ) (hC : 1 ≤ C) (hq : 48 * C ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (u x : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G u)
    (hUX : G.Adj u x) (hNonhigh : 0 ≤ signedDeficiency q G x)
    (hNonlight : (G.neighborFinset x ∩ nonlightLowVertices q T G).card ≤ M)
    (hRow : ((positivePartners q G x).card : ℤ) ≤ signedDeficiency q G u + B)
    (hNoCheap : ∀ v w (hvw : v ≠ w), ¬G.Adj v w →
      q ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4)) :
    signedDeficiency q G u ≤ 16 * (C : ℤ) *
      (3 * M + 4 * B + 3 * (highVertices q G).card + (lightTriangleRegularVertices q T G).card + 3) := by
  let k := signedDeficiency q G u
  let L : ℤ := 8 * C
  let R : ℤ := 3 * (highVertices q G).card + (lightTriangleRegularVertices q T G).card
  have hComparison := small_neighbor_row_comparison q C T M B hC G hFree hDegree hDense
    u x hLow hUX hNonhigh hNonlight hRow hNoCheap
  change L * ((k - 3 - M) * (q : ℤ) - R - 2 * M) ≤
    (k + B) * ((L - 1) * (q : ℤ) + 3 * L) at hComparison
  have hqInt : (1 : ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hSix : 6 * L ≤ (q : ℤ) := by
    have h : (48 : ℤ) * C ≤ q := by exact_mod_cast hq
    dsimp [L]
    linarith only [h]
  have hNumeric := growing_neighbor_numeric_bound q k L M B R hqInt hL hSix
    (by dsimp [k]; omega) (Nat.cast_nonneg M) (Nat.cast_nonneg B) (by dsimp [R]; positivity) hComparison
  dsimp only [k, L, R] at hNumeric
  convert hNumeric using 1
  ring

/-- At a regular vertex, one low hub adds at most its own deficiency to the bounded row contribution. -/
theorem regular_positive_row_one_hub (q T K M : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hIndependent : ∀ v ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj v w)
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (u x : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G u)
    (hRegular : signedDeficiency q G x = 0)
    (hOnlyHub : ∀ w ∈ G.neighborFinset x, w ≠ u → w ∉ lowHubs q T G)
    (hNonlight : (G.neighborFinset x ∩ nonlightLowVertices q T G).card ≤ M) :
    ((positivePartners q G x).card : ℤ) ≤ signedDeficiency q G u +
      (1 + (lightTriangleRegularVertices q T G).card + (highVertices q G).card + ((K : ℤ) + 1) * M) := by
  let N := G.neighborFinset x ∩ nonlightLowVertices q T G
  let k := signedDeficiency q G u
  have hK : (0 : ℤ) ≤ K := by positivity
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hEach (w) (hw : w ∈ N) : positiveDeficiency q G w ≤ (K : ℤ) + (if w = u then k else 0) := by
    by_cases hEq : w = u
    · subst w
      have hPositive : positiveDeficiency q G u = k := max_eq_left (by omega)
      rw [hPositive, ite_eq_left rfl]
      omega
    · rw [ite_eq_right hEq, add_zero]
      apply max_le
      · exact hOutside w (hOnlyHub w (Finset.mem_inter.mp hw).1 hEq)
      · exact hK
  have hSum := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib] at hSum
  have hSingle : (∑ w ∈ N, if w = u then k else 0) ≤ k := by
    by_cases hu : u ∈ N
    · simp [hu]
    · simpa [hu] using hk
  have hWeight : (∑ w ∈ N, positiveDeficiency q G w) ≤ (K : ℤ) * N.card + k := by
    simp only [Finset.sum_const, nsmul_eq_mul] at hSum
    nlinarith only [hSum, hSingle]
  have hMass := regular_negativeResidualMass_le q T G hFree x hRegular
  have hTriangles : ((triangularLightNeighbors q T G x).card : ℤ) ≤
      (lightTriangleRegularVertices q T G).card + (highVertices q G).card + N.card := by
    exact_mod_cast triangular_light_neighbor_card_le q T G hFree hIndependent x
  have hP := positivePartners_card_le_mass q G x
  rw [positiveResidualMass_balance] at hP
  have hNBound : (N.card : ℤ) ≤ M := by dsimp [N]; exact_mod_cast hNonlight
  have hScaled := mul_le_mul_of_nonneg_left hNBound (show 0 ≤ (K : ℤ) + 1 by positivity)
  change _ ≤ k + _
  change _ ≤ (triangularLightNeighbors q T G x).card + (∑ w ∈ N, positiveDeficiency q G w) at hMass
  nlinarith only [hWeight, hMass, hTriangles, hP, hScaled]

/-- A vertex of sufficiently large deficiency has only boundedly many regular neighbors. -/
theorem large_deficiency_regular_neighbors_card_le (q C T K M B : ℕ)
    (hC : 1 ≤ C) (hq : 48 * C ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hIndependent : ∀ v ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj v w)
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (hNonlight : ∀ w, w ∉ lowHubs q T G → (G.neighborFinset w ∩ nonlightLowVertices q T G).card ≤ M)
    (hB : 1 + (lightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M ≤ B)
    (hNoCheap : ∀ v w (hvw : v ≠ w), ¬G.Adj v w →
      q ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4))
    (u : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G u)
    (hLarge : 16 * (C : ℤ) * (3 * M + 4 * B + 3 * (highVertices q G).card +
      (lightTriangleRegularVertices q T G).card + 3) < signedDeficiency q G u) :
    (regularNeighbors q G u).card ≤ (lowHubs q T G).card := by
  let U := (lowHubs q T G).erase u
  let hits := (G.neighborFinset u).filter fun x => ∃ w ∈ U, G.Adj x w
  have hHits : hits.card ≤ (lowHubs q T G).card := by
    have h := neighbor_hits_set_card_le G hFree u (G.neighborFinset u) U (fun _ h => h) (by simp [U])
    exact h.trans (Finset.card_le_card (Finset.erase_subset _ _))
  have hSubset : regularNeighbors q G u ⊆ hits := by
    intro x hx
    obtain ⟨hxN, hxRegular⟩ := Finset.mem_filter.mp hx
    have hUX := (G.mem_neighborFinset u x).mp hxN
    have hxNotHub : x ∉ lowHubs q T G := by
      intro h
      have hPositive := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
      omega
    by_contra hxNotHits
    have hOnly : ∀ w ∈ G.neighborFinset x, w ≠ u → w ∉ lowHubs q T G := by
      intro w hw hwu hwHub
      have hwU : w ∈ U := Finset.mem_erase.mpr ⟨hwu, hwHub⟩
      exact hxNotHits (Finset.mem_filter.mpr ⟨hxN, w, hwU, (G.mem_neighborFinset x w).mp hw⟩)
    have hRow := regular_positive_row_one_hub q T K M G hFree hIndependent hOutside u x hLow hxRegular
      hOnly (hNonlight x hxNotHub)
    have hBInt : 1 + ((lightTriangleRegularVertices q T G).card : ℤ) + (highVertices q G).card +
        ((K : ℤ) + 1) * M ≤ B := by exact_mod_cast hB
    have hSmall : ((positivePartners q G x).card : ℤ) ≤ signedDeficiency q G u + B := by omega
    have hBound := small_neighbor_row_bounds_deficiency q C T M B hC hq G hFree hDegree hDense u x hLow
      hUX (by omega) (hNonlight x hxNotHub) hSmall hNoCheap
    exact (not_le_of_gt hLarge) hBound
  exact (Finset.card_le_card hSubset).trans hHits

/-- Induced low degrees over one low neighborhood have a linear total bound. -/
theorem sum_low_neighbor_low_degrees_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (u : Fin n) :
    (∑ x ∈ lowNeighbors q G u, (lowNeighbors q G x).card) ≤
      (lowVertices q G).card + (lowNeighbors q G u).card := by
  let Q := lowNeighbors q G u
  let S := lowVertices q G
  have hSum := sum_neighbor_intersection_card G Q S
  have hLeft : (∑ x ∈ Q, (G.neighborFinset x ∩ S).card) = ∑ x ∈ Q, (lowNeighbors q G x).card := by
    apply Finset.sum_congr rfl
    intro x _
    rw [lowNeighbors_eq_inter]
  rw [hLeft] at hSum
  have hEach (y) (_hy : y ∈ S) : (G.neighborFinset y ∩ Q).card ≤ 1 + (if y = u then Q.card else 0) := by
    by_cases hEq : y = u
    · rw [ite_eq_left hEq]
      exact (Finset.card_le_card Finset.inter_subset_right).trans (by omega)
    · rw [ite_eq_right hEq, add_zero]
      have hSubset : G.neighborFinset y ∩ Q ⊆ G.neighborFinset y ∩ G.neighborFinset u := by
        intro z hz
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).1⟩
      exact (Finset.card_le_card hSubset).trans (codegree_le_one G hFree y u hEq)
  have hCount := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib] at hCount
  by_cases hu : u ∈ S
  · simp [hu] at hCount
    change (∑ x ∈ Q, (lowNeighbors q G x).card) ≤ S.card + Q.card
    omega
  · simp [hu] at hCount
    change (∑ x ∈ Q, (lowNeighbors q G x).card) ≤ S.card + Q.card
    omega

/-- Many low neighbors leave one outside the hubs with a bounded low degree and no second hub neighbor. -/
theorem exists_small_low_neighbor (q T R : ℕ) (hR : 1 ≤ R) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hLowSize : ((lowVertices q G).card : ℤ) ≤ 3 * q)
    (u : Fin (q ^ 2 + q + 2)) (hMin : q ≤ R * G.degree u)
    (hRegular : (regularNeighbors q G u).card ≤ (lowHubs q T G).card)
    (hOrder : 2 * (R : ℤ) * (3 * (lowHubs q T G).card + (highVertices q G).card) ≤ q) :
    ∃ x ∈ lowNeighbors q G u, x ∉ lowHubs q T G ∧
      (∀ w ∈ G.neighborFinset x, w ≠ u → w ∉ lowHubs q T G) ∧
      (lowNeighbors q G x).card ≤ 10 * R := by
  let U := lowHubs q T G
  let hits := (G.neighborFinset u).filter fun x => ∃ w ∈ U.erase u, G.Adj x w
  let Q := lowNeighbors q G u \ (U ∪ hits)
  have hHits : hits.card ≤ U.card := by
    have h := neighbor_hits_set_card_le G hFree u (G.neighborFinset u) (U.erase u)
      (fun _ h => h) (by simp)
    exact h.trans (Finset.card_le_card (Finset.erase_subset _ _))
  have hQSubset : Q ⊆ lowNeighbors q G u := Finset.sdiff_subset
  have hRemoval : ((lowNeighbors q G u).card : ℤ) ≤ Q.card + 2 * U.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := lowNeighbors q G u) (t := U ∪ hits)
    have hUnion := Finset.card_union_le U hits
    change (lowNeighbors q G u).card ≤ Q.card + (U ∪ hits).card at h
    exact_mod_cast (show (lowNeighbors q G u).card ≤ Q.card + 2 * U.card by omega)
  have hRegularInt : ((regularNeighbors q G u).card : ℤ) ≤ U.card := by exact_mod_cast hRegular
  have hLowDegree := regular_neighbor_card_lower q G u
  have hMinInt : (q : ℤ) ≤ (R : ℤ) * G.degree u := by exact_mod_cast hMin
  have hRInt : (1 : ℤ) ≤ R := by exact_mod_cast hR
  have hDegreeBound : (G.degree u : ℤ) ≤ Q.card + 3 * U.card + (highVertices q G).card := by omega
  have hDegreeScaled := mul_le_mul_of_nonneg_left hDegreeBound (show 0 ≤ (R : ℤ) by omega)
  have hQSize : (q : ℤ) ≤ 2 * (R : ℤ) * Q.card := by
    change 2 * (R : ℤ) * (3 * U.card + (highVertices q G).card) ≤ q at hOrder
    nlinarith only [hMinInt, hDegreeScaled, hOrder]
  have hQPositive : 0 < Q.card := by
    by_contra h
    have hZero : Q.card = 0 := by omega
    rw [hZero, Nat.cast_zero, mul_zero] at hQSize
    have hqInt : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
    omega
  have hTotal := sum_low_neighbor_low_degrees_le q G hFree u
  have hSelected : (∑ x ∈ Q, (lowNeighbors q G x).card) ≤
      (lowVertices q G).card + (lowNeighbors q G u).card := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hQSubset (fun _ _ _ => Nat.zero_le _)).trans hTotal
  have hLowCap : (lowNeighbors q G u).card ≤ q + 2 := by
    have h := Finset.card_le_card (Finset.filter_subset (fun w => 0 < signedDeficiency q G w) (G.neighborFinset u))
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h
    exact h.trans (hDegree u)
  have hSelectedInt : (∑ x ∈ Q, ((lowNeighbors q G x).card : ℤ)) ≤ 5 * (q : ℤ) := by
    have h := hSelected
    have hCast : (∑ x ∈ Q, ((lowNeighbors q G x).card : ℤ)) ≤
        ((lowVertices q G).card : ℤ) + (lowNeighbors q G u).card := by exact_mod_cast h
    have hCap : ((lowNeighbors q G u).card : ℤ) ≤ (q : ℤ) + 2 := by exact_mod_cast hLowCap
    have hqInt : (2 : ℤ) ≤ q := by exact_mod_cast hq
    omega
  have hExists : ∃ x ∈ Q, (lowNeighbors q G x).card ≤ 10 * R := by
    by_contra h
    push Not at h
    have hEach (x) (hx : x ∈ Q) : 10 * (R : ℤ) + 1 ≤ (lowNeighbors q G x).card := by
      have hBad := h x hx
      exact_mod_cast (show 10 * R + 1 ≤ (lowNeighbors q G x).card by omega)
    have hSum := Finset.sum_le_sum hEach
    simp only [Finset.sum_const, nsmul_eq_mul] at hSum
    have hPos : (0 : ℤ) < Q.card := by exact_mod_cast hQPositive
    nlinarith only [hSum, hSelectedInt, hQSize, hPos]
  obtain ⟨x, hx, hxSmall⟩ := hExists
  obtain ⟨hxLow, hxNot⟩ := Finset.mem_sdiff.mp hx
  have hxNotHub : x ∉ U := fun h => hxNot (Finset.mem_union_left _ h)
  have hxNotHits : x ∉ hits := fun h => hxNot (Finset.mem_union_right _ h)
  refine ⟨x, hxLow, hxNotHub, ?_, hxSmall⟩
  intro w hw hwu hwHub
  have hwU : w ∈ U.erase u := Finset.mem_erase.mpr ⟨hwu, hwHub⟩
  exact hxNotHits (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxLow).1, w, hwU,
    (G.mem_neighborFinset x w).mp hw⟩)

/-- One exceptional neighboring low contributes at most its deficiency beyond the bounded low-degree weight. -/
theorem neighbor_positive_weight_one_exception {n : ℕ} (q K : ℕ) (G : SimpleGraph (Fin n))
    (u x : Fin n) (hLow : 1 ≤ signedDeficiency q G u)
    (hOther : ∀ w ∈ G.neighborFinset x, w ≠ u → signedDeficiency q G w ≤ K) :
    (∑ w ∈ G.neighborFinset x, positiveDeficiency q G w) ≤
      signedDeficiency q G u + (K : ℤ) * (lowNeighbors q G x).card := by
  let S := lowNeighbors q G x
  let k := signedDeficiency q G u
  have hEach (w) (hw : w ∈ S) : signedDeficiency q G w ≤ (K : ℤ) + (if w = u then k else 0) := by
    by_cases hEq : w = u
    · subst w
      simp only [ite_true]
      dsimp [k]
      omega
    · rw [ite_eq_right hEq, add_zero]
      exact hOther w (Finset.mem_filter.mp hw).1 hEq
  have hSum := Finset.sum_le_sum hEach
  rw [sum_lowNeighbors_deficiency, Finset.sum_add_distrib] at hSum
  have hSingle : (∑ w ∈ S, if w = u then k else 0) ≤ k := by
    by_cases hu : u ∈ S
    · simp [hu]
    · have hk : 0 ≤ k := by dsimp [k]; omega
      simpa [hu] using hk
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  change _ ≤ k + (K : ℤ) * S.card
  nlinarith only [hSum, hSingle]

theorem adjacent_low_positive_weight_lower {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (u x : Fin n) (hLow : 1 ≤ signedDeficiency q G u) (hAdj : G.Adj x u) :
    signedDeficiency q G u ≤ ∑ w ∈ G.neighborFinset x, positiveDeficiency q G w := by
  have h := Finset.single_le_sum (fun w (_ : w ∈ G.neighborFinset x) => positiveDeficiency_nonnegative q G w)
    ((G.mem_neighborFinset x u).mpr hAdj)
  have hPositive : positiveDeficiency q G u = signedDeficiency q G u := max_eq_left (by omega)
  rwa [hPositive] at h

theorem unit_row_upper_one_exception (q K D : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (u x : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G u)
    (hUnit : signedDeficiency q G x = 1) (hFew : (lowNeighbors q G x).card ≤ D)
    (hTriangles : (triangularRegularNeighbors q G x).card ≤ 16)
    (hOther : ∀ w ∈ G.neighborFinset x, w ≠ u → signedDeficiency q G w ≤ K) :
    ((positivePartners q G x).card : ℤ) ≤ signedDeficiency q G u +
      (17 + ((K : ℤ) + 1) * D + (highVertices q G).card) := by
  have hWeight := neighbor_positive_weight_one_exception q K G u x hLow hOther
  have hRow := low_positivePartners_card_upper q G hFree x (by omega)
  rw [hUnit, triangle_codegree_sum_eq_card G hFree x] at hRow
  have hTri := (triangular_neighbor_card_bounds q G x).2
  have hTriInt : ((triangularNeighbors G x).card : ℤ) ≤
      (triangularRegularNeighbors q G x).card + (lowNeighbors q G x).card + (highVertices q G).card := by exact_mod_cast hTri
  have hSmallTri : ((triangularRegularNeighbors q G x).card : ℤ) ≤ 16 := by exact_mod_cast hTriangles
  have hFewInt : ((lowNeighbors q G x).card : ℤ) ≤ D := by exact_mod_cast hFew
  have hScaled := mul_le_mul_of_nonneg_left hFewInt (show 0 ≤ (K : ℤ) + 1 by positivity)
  nlinarith only [hWeight, hRow, hTriInt, hSmallTri, hScaled]

/-- A nonunit low, or a heavy unit low, next to u has a positive row of size at least q plus the deficiency of u. -/
theorem low_row_lower_next_to_exception (q D : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * q)
    (u x : Fin (q ^ 2 + q + 2)) (hLowU : 1 ≤ signedDeficiency q G u)
    (hLowX : 1 ≤ signedDeficiency q G x) (hAdj : G.Adj x u)
    (hFew : (lowNeighbors q G x).card ≤ D)
    (hHeavy : signedDeficiency q G x = 1 → (q : ℤ) < 2 * (triangularRegularNeighbors q G x).card) :
    (q : ℤ) + signedDeficiency q G u - D - 2 * (highVertices q G).card - 9 ≤
      ((positivePartners q G x).card : ℤ) := by
  have hWeight := adjacent_low_positive_weight_lower q G u x hLowU hAdj
  have hSigned := neighbor_positiveDeficiency_le_signed_add_high q G hDegree x
  have hRow := low_positivePartners_card_lower q G hFree hDegree x hLowX
  rw [triangle_codegree_sum_eq_card G hFree x] at hRow
  have hFewInt : ((lowNeighbors q G x).card : ℤ) ≤ D := by exact_mod_cast hFew
  have hH : (0 : ℤ) ≤ (highVertices q G).card := by positivity
  have hTau : (0 : ℤ) ≤ (triangularNeighbors G x).card := by positivity
  by_cases hUnit : signedDeficiency q G x = 1
  · let t : ℤ := (triangularRegularNeighbors q G x).card
    let r : ℤ := (regularNeighbors q G x).card
    have hDegreeX : (G.degree x : ℤ) = q := by unfold signedDeficiency at hUnit; omega
    have hRegular := regular_neighbor_card_lower q G x
    rw [hDegreeX] at hRegular
    change (q : ℤ) - (lowNeighbors q G x).card - (highVertices q G).card ≤ r at hRegular
    have hCover := triangle_cover_bound q G hFree x hLowX
    rw [hUnit, hDegreeX, one_mul] at hCover
    change t * (r - t - 1) ≤ (q : ℤ) + _ at hCover
    have hBig : (q : ℤ) < 2 * t := hHeavy hUnit
    have ht : 0 < t := by
      have hq : (0 : ℤ) ≤ q := by positivity
      omega
    have hProduct : t * (r - t - 1) ≤ t * 8 := by nlinarith only [hCover, hTotal, hBig]
    have hRest : r - t - 1 ≤ 8 := (mul_le_mul_iff_of_pos_left ht).mp hProduct
    have hTri : t ≤ (triangularNeighbors G x).card := by
      dsimp [t]
      exact_mod_cast (triangular_neighbor_card_bounds q G x).1
    rw [hUnit] at hRow
    nlinarith only [hWeight, hSigned, hRow, hRegular, hRest, hTri, hFewInt]
  · have hTwo : 2 ≤ signedDeficiency q G x := by omega
    have hExtra := mul_nonneg (show 0 ≤ signedDeficiency q G x - 2 by omega) (Nat.cast_nonneg (α := ℤ) q)
    nlinarith only [hWeight, hSigned, hRow, hExtra, hTwo, hTau, hH, Nat.cast_nonneg (α := ℤ) D]

/-- Positive low partners of x exclude all low neighbors of a common adjacent vertex u. -/
theorem positive_low_partners_disjoint_neighbor_set (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (u x : Fin (q ^ 2 + q + 2)) (hLowX : 1 ≤ signedDeficiency q G x) (hAdj : G.Adj u x) :
    (lowPositivePartners q G x).card + (lowNeighbors q G u).card ≤ (lowVertices q G).card := by
  have hDisjoint : Disjoint (lowPositivePartners q G x) (lowNeighbors q G u) := by
    apply Finset.disjoint_left.mpr
    intro y hyP hyN
    obtain ⟨hyPositive, hyLow⟩ := Finset.mem_filter.mp hyP
    obtain ⟨_, _, hyZero⟩ := positivePartner_nonhigh q G x y hLowX (by omega) hyPositive
    exact (codegree_eq_zero_iff G x y).mp hyZero u hAdj.symm ((G.mem_neighborFinset u y).mp (Finset.mem_filter.mp hyN).1).symm
  have hSubset : lowPositivePartners q G x ∪ lowNeighbors q G u ⊆ lowVertices q G := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
  rw [← Finset.card_union_of_disjoint hDisjoint]
  exact Finset.card_le_card hSubset

theorem total_positive_weight_with_one_large_low {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (u : Fin n) (hLow : 1 ≤ signedDeficiency q G u) :
    ((lowVertices q G).card : ℤ) + signedDeficiency q G u - 1 ≤ ∑ v, positiveDeficiency q G v := by
  let S := lowVertices q G
  have hu : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hEach (v) (hv : v ∈ S.erase u) : (1 : ℤ) ≤ positiveDeficiency q G v := by
    have hPositive := (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
    unfold positiveDeficiency
    omega
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hSum
  have hPartition := Finset.sum_erase_add S (positiveDeficiency q G) hu
  have hCard := Finset.card_erase_add_one hu
  have hPositive : positiveDeficiency q G u = signedDeficiency q G u := max_eq_left (by omega)
  rw [hPositive] at hPartition
  have hTotal : (∑ v ∈ S, positiveDeficiency q G v) ≤ ∑ v, positiveDeficiency q G v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro v _ _
    exact positiveDeficiency_nonnegative q G v
  have hCardInt : ((S.erase u).card : ℤ) + 1 = S.card := by exact_mod_cast hCard
  change (S.card : ℤ) + _ - 1 ≤ _
  linarith only [hSum, hPartition, hTotal, hCardInt]

/-- The prepared low-vertex structure and positive-row propagation bound all vertex deficiencies. -/
theorem signedDeficiency_bounded_of_structure (q C T K M R B₀ B₁ Q : ℕ)
    (hC : 1 ≤ C) (hR : 1 ≤ R) (hq : 48 * C ≤ q) (hqTwo : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q) (hMin : ∀ v, q ≤ R * G.degree v)
    (hIndependent : ∀ v ∈ lightLowVertices q T G, ∀ w ∈ lightLowVertices q T G, ¬G.Adj v w)
    (hOutside : ∀ w, w ∉ lowHubs q T G → signedDeficiency q G w ≤ K)
    (hNonlight : ∀ w, w ∉ lowHubs q T G → (G.neighborFinset w ∩ nonlightLowVertices q T G).card ≤ M)
    (hGood : ∀ x, 1 ≤ signedDeficiency q G x → x ∉ lowHubs q T G → (regularPositivePartners q G x).card ≤ Q)
    (hB₀ : 1 + (lightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M ≤ B₀)
    (hB₁ : 17 + (K + 1) * (10 * R) + (highVertices q G).card ≤ B₁)
    (hSelect : 2 * (R : ℤ) * (3 * (lowHubs q T G).card + (highVertices q G).card) ≤ q)
    (hFew : 8 * (10 * R) ≤ q) (hHighOrder : 8 * ((highVertices q G).card + 1) ≤ q)
    (hNoCheap : ∀ v w (hvw : v ≠ w), ¬G.Adj v w →
      q ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4))
    (u : Fin (q ^ 2 + q + 2)) :
    let H : ℤ := (highVertices q G).card
    let U : ℤ := (lowHubs q T G).card
    let J : ℤ := (lightTriangleRegularVertices q T G).card
    signedDeficiency q G u ≤ max
      (max (16 * (C : ℤ) * (3 * M + 4 * B₀ + 3 * H + J + 3))
        (16 * (C : ℤ) * (3 * M + 4 * B₁ + 3 * H + J + 3)))
      (10 * R + 5 * H + U + Q + 10) := by
  let H : ℤ := (highVertices q G).card
  let U : ℤ := (lowHubs q T G).card
  let J : ℤ := (lightTriangleRegularVertices q T G).card
  let A₀ := 16 * (C : ℤ) * (3 * M + 4 * B₀ + 3 * H + J + 3)
  let A₁ := 16 * (C : ℤ) * (3 * M + 4 * B₁ + 3 * H + J + 3)
  let A₂ := (10 : ℤ) * R + 5 * H + U + Q + 10
  let k := signedDeficiency q G u
  change k ≤ max (max A₀ A₁) A₂
  by_contra h
  have hLarge : max (max A₀ A₁) A₂ < k := lt_of_not_ge h
  have hLarge₀ : A₀ < k := ((le_max_left A₀ A₁).trans (le_max_left (max A₀ A₁) A₂)).trans_lt hLarge
  have hLarge₁ : A₁ < k := ((le_max_right A₀ A₁).trans (le_max_left (max A₀ A₁) A₂)).trans_lt hLarge
  have hLarge₂ : A₂ < k := (le_max_right (max A₀ A₁) A₂).trans_lt hLarge
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂, H, U]; positivity
  have hLowU : 1 ≤ signedDeficiency q G u := by change 1 ≤ k; omega
  have hRegular := large_deficiency_regular_neighbors_card_le q C T K M B₀ hC hq G hFree hDegree hDense
    hIndependent hOutside hNonlight hB₀ hNoCheap u hLowU hLarge₀
  obtain ⟨x, hxLow, hxNotHub, hOnlyHub, hxFew⟩ := exists_small_low_neighbor q T R hR hqTwo G hFree hDegree
    (dense_lowVertices_card_le q G hDegree hDense hHigh) u (hMin u) hRegular hSelect
  have hUX := (G.mem_neighborFinset u x).mp (Finset.mem_filter.mp hxLow).1
  have hLowX : 1 ≤ signedDeficiency q G x := by have h := (Finset.mem_filter.mp hxLow).2; omega
  have hOther : ∀ w ∈ G.neighborFinset x, w ≠ u → signedDeficiency q G w ≤ K :=
    fun w hw hwu => hOutside w (hOnlyHub w hw hwu)
  have hTotal := dense_positiveDeficiency_le_high_card q G hDegree hDense
  have hHighInt : H ≤ q := by dsimp [H]; exact_mod_cast hHigh
  have hF : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ) := by
    change _ ≤ 2 * (q : ℤ) + H - 4 at hTotal
    omega
  have hHeavy : signedDeficiency q G x = 1 → (q : ℤ) < 2 * (triangularRegularNeighbors q G x).card := by
    intro hUnit
    have hBigTri : 16 < (triangularRegularNeighbors q G x).card := by
      by_contra hSmall
      have hTriangles : (triangularRegularNeighbors q G x).card ≤ 16 := by omega
      have hRow := unit_row_upper_one_exception q K (10 * R) G hFree u x hLowU hUnit hxFew hTriangles hOther
      have hBInt : (17 : ℤ) + ((K : ℤ) + 1) * (10 * R) + H ≤ B₁ := by dsimp [H]; exact_mod_cast hB₁
      push_cast at hRow hBInt
      have hSmallRow : ((positivePartners q G x).card : ℤ) ≤ signedDeficiency q G u + B₁ := by
        dsimp only [H] at hBInt
        nlinarith only [hRow, hBInt]
      have hBound := small_neighbor_row_bounds_deficiency q C T M B₁ hC hq G hFree hDegree hDense u x hLowU
        hUX (by omega) (hNonlight x hxNotHub) hSmallRow hNoCheap
      exact (not_le_of_gt hLarge₁) hBound
    by_contra hNotHeavy
    have hFewX : 8 * ((lowNeighbors q G x).card : ℤ) ≤ q := by
      have hA : ((lowNeighbors q G x).card : ℤ) ≤ 10 * R := by exact_mod_cast hxFew
      have hB : (8 : ℤ) * (10 * R) ≤ q := by exact_mod_cast hFew
      omega
    have hHighX : 8 * (((highVertices q G).card : ℤ) + 1) ≤ q := by exact_mod_cast hHighOrder
    have hTriangles := light_unit_triangle_bound q (by omega) G hFree x hUnit hFewX hHighX hF (by omega)
    omega
  have hRowLower := low_row_lower_next_to_exception q (10 * R) G hFree hDegree hF u x hLowU hLowX hUX.symm hxFew hHeavy
  push_cast at hRowLower
  have hLowPartners := positive_low_partners_disjoint_neighbor_set q G u x hLowX hUX
  have hRegularX := hGood x hLowX hxNotHub
  have hHighX := highPositivePartners_card_le q G x
  have hPartition := positive_partner_partition_card q G x
  have hUpper : ((positivePartners q G x).card : ℤ) + (lowNeighbors q G u).card ≤
      (lowVertices q G).card + Q + H := by
    dsimp [H]
    exact_mod_cast (show (positivePartners q G x).card + (lowNeighbors q G u).card ≤
      (lowVertices q G).card + Q + (highVertices q G).card by omega)
  have hRegularInt : ((regularNeighbors q G u).card : ℤ) ≤ U := by dsimp [U]; exact_mod_cast hRegular
  have hLowDegree := regular_neighbor_card_lower q G u
  have hDegreeEq : (G.degree u : ℤ) = (q : ℤ) + 1 - k := by dsimp [k]; unfold signedDeficiency; ring
  rw [hDegreeEq] at hLowDegree
  have hExtra := total_positive_weight_with_one_large_low q G u hLowU
  change (q : ℤ) + k - 10 * R - 2 * H - 9 ≤ ((positivePartners q G x).card : ℤ) at hRowLower
  change (q : ℤ) + 1 - k - (lowNeighbors q G u).card - H ≤ _ at hLowDegree
  change (lowVertices q G).card + k - 1 ≤ _ at hExtra
  dsimp [A₂] at hLarge₂
  omega

/-- Arbitrarily large counterexamples at every positive constant refute the bound. -/
theorem refutes_bound_of_witnesses
    (hWitness : ∀ c : ℝ, 0 < c → ∀ N : ℕ,
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N ≤ n ∧
        extremalNumber n (cycleGraph 4) < G.edgeSet.ncard ∧
        (fourCycleCopies G : ℝ) < c * Real.sqrt (n : ℝ)) :
    ¬ ClaimedBound := by
  classical
  rintro ⟨c, hc, hEventually⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  obtain ⟨n, G, hn, hEdges, hCycles⟩ := hWitness c hc N
  have hEdges' : extremalNumber n (cycleGraph 4) < G.edgeFinset.card := by
    simpa only [edgeSet_ncard] using hEdges
  exact (not_lt_of_ge (hN n hn G hEdges')) hCycles

/-- The above-plane orders are large whenever the parameter is large. -/
theorem above_plane_order_ge (q : ℕ) : q ≤ q ^ 2 + q + 2 := by
  omega

/-- At these orders, a cycle count small relative to q is small relative to sqrt n. -/
theorem parameter_le_sqrt_order (q : ℕ) :
    (q : ℝ) ≤ Real.sqrt ((q ^ 2 + q + 2 : ℕ) : ℝ) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  push_cast
  nlinarith

/-- The split construction's numerical cycle count has the required quadratic bound. -/
theorem split_count_bound (a : ℕ) (q δ : ℝ)
    (hq : 0 < q) (hδ : 0 ≤ δ)
    (ha : (a : ℝ) ≤ δ * Real.sqrt q) :
    (a.choose 2 : ℝ) / q ≤ δ ^ 2 / 2 := by
  have hsq : (a : ℝ) ^ 2 ≤ (δ * Real.sqrt q) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg a) (mul_nonneg hδ (Real.sqrt_nonneg q))).2 ha
  have hroot : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  rw [div_le_iff₀ hq, Nat.cast_choose_two]
  rw [mul_pow, hroot] at hsq
  nlinarith [Nat.cast_nonneg (α := ℝ) a]

/-- Quantitative form of the numerical dichotomy in the proposed proof. -/
theorem cycle_count_bound_of_dichotomy (a : ℕ) (q γ δ : ℝ)
    (hq : 0 < q) (hδ : 0 ≤ δ)
    (hsmall : min ((a : ℝ) / Real.sqrt q) (γ / q) ≤ δ) :
    min ((a.choose 2 : ℝ) / q) (γ / q) ≤ max (δ ^ 2 / 2) δ := by
  rcases min_le_iff.mp hsmall with ha | hγ
  · have ha' : (a : ℝ) ≤ δ * Real.sqrt q :=
      (div_le_iff₀ (Real.sqrt_pos.2 hq)).1 ha
    exact (min_le_left _ _).trans ((split_count_bound a q δ hq hδ ha').trans
      (le_max_left _ _))
  · exact (min_le_right _ _).trans (hγ.trans (le_max_right _ _))

/-- This is the exact analytic consequence needed from the manuscript's dichotomy. -/
theorem refutes_bound_of_above_plane_witnesses
    (hWitness : ∀ c : ℝ, 0 < c → ∀ Q : ℕ,
      ∃ (q : ℕ) (G : SimpleGraph (Fin (q ^ 2 + q + 2))),
        Q ≤ q ∧
        extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) < G.edgeSet.ncard ∧
        (fourCycleCopies G : ℝ) < c * (q : ℝ)) :
    ¬ ClaimedBound := by
  apply refutes_bound_of_witnesses
  intro c hc N
  obtain ⟨q, G, hq, hEdges, hCycles⟩ := hWitness c hc N
  refine ⟨q ^ 2 + q + 2, G, hq.trans (above_plane_order_ge q), hEdges, ?_⟩
  exact hCycles.trans_le (mul_le_mul_of_nonneg_left (parameter_le_sqrt_order q) hc.le)

/-- A claimed square-root lower bound supplies a uniform integer-scaled bound at every large order. -/
theorem claimedBound_scaled_lower (hBound : ClaimedBound) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      ∀ H : SimpleGraph (Fin (q ^ 2 + q + 2)),
        extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) < H.edgeFinset.card →
          q ≤ C * fourCycleCopies H := by
  obtain ⟨c, hc, hEventually⟩ := hBound
  obtain ⟨C, hC⟩ := exists_nat_gt (1 / c)
  have hScale : 1 < (C : ℝ) * c := (div_lt_iff₀ hc).mp hC
  have hCPositive : 0 < C := by
    by_contra h
    have hZero : C = 0 := by omega
    simp [hZero] at hScale
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  refine ⟨C, by omega, N, ?_⟩
  intro q hq H hEdges
  have hOrder : N ≤ q ^ 2 + q + 2 := hq.trans (above_plane_order_ge q)
  have hCount := hN _ hOrder H hEdges
  have hLower : c * (q : ℝ) ≤ (fourCycleCopies H : ℝ) :=
    (mul_le_mul_of_nonneg_left (parameter_le_sqrt_order q) hc.le).trans hCount
  have hScaled := mul_le_mul_of_nonneg_left hLower (Nat.cast_nonneg (α := ℝ) C)
  have hUnit := mul_le_mul_of_nonneg_right hScale.le (Nat.cast_nonneg (α := ℝ) q)
  have hResult : (q : ℝ) ≤ (C : ℝ) * fourCycleCopies H := by nlinarith
  exact_mod_cast hResult

/-- The split graph forces the excess to grow under the claimed lower bound. -/
theorem scaled_lower_forces_excess (C k : ℕ) (hC : 1 ≤ C) (hk : k ≠ 0)
    (hLower : ∀ H : SimpleGraph (Fin ((2 ^ k) ^ 2 + 2 ^ k + 2)),
      extremalNumber ((2 ^ k) ^ 2 + 2 ^ k + 2) (cycleGraph 4) < H.edgeFinset.card →
        2 ^ k ≤ C * fourCycleCopies H) :
    2 ^ k ≤ 4 * C * abovePlaneExcess (2 ^ k) ^ 2 := by
  by_cases hSmall : abovePlaneExcess (2 ^ k) ≤ 2 ^ k
  · obtain ⟨H, hEdges, hCycles⟩ := split_witness_at_extremal_threshold k hk hSmall
    have h := hLower H (by omega)
    have hUpper := Nat.mul_le_mul_left C hCycles
    nlinarith
  · have hLarge : 2 ^ k < abovePlaneExcess (2 ^ k) := by omega
    have hPositive := abovePlaneExcess_lower k hk
    have hSquare : abovePlaneExcess (2 ^ k) ≤ abovePlaneExcess (2 ^ k) ^ 2 := by nlinarith
    have hProduct := Nat.mul_le_mul_right (abovePlaneExcess (2 ^ k) ^ 2) hC
    nlinarith

/-- Under the claimed bound, all large dyadic extremizers satisfy the finite preparation estimates. -/
theorem claimedBound_uniform_preparation (hBound : ClaimedBound) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ 2 ^ k →
      2 ^ k ≤ 4 * C * abovePlaneExcess (2 ^ k) ^ 2 ∧
      ∀ G : SimpleGraph (Fin ((2 ^ k) ^ 2 + 2 ^ k + 2)),
        (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ k) ^ 2 + 2 ^ k + 2) (cycleGraph 4) →
        (∀ v w (hvw : v ≠ w), ¬G.Adj v w →
          2 ^ k ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4)) ∧
        (∀ v, 2 ^ k ≤ (16 * C) * G.degree v) ∧
        (∀ v, G.degree v ≤ 2 ^ k + 2) ∧
        (highVertices (2 ^ k) G).card ≤ 2611456 * C ∧
        (∑ v, positiveDeficiency (2 ^ k) G v) ≤ 2 * (2 ^ k : ℕ) + (5222912 : ℤ) * C := by
  obtain ⟨C, hC, N, hLower⟩ := claimedBound_scaled_lower hBound
  let threshold := N + 8 + 327000 * (16 * C) ^ 2 + 16 * C + 1
  refine ⟨C, hC, threshold, ?_⟩
  intro k hk
  have hN : N ≤ 2 ^ k := by dsimp [threshold] at hk; omega
  have hq : 8 ≤ 2 ^ k := by dsimp [threshold] at hk; omega
  have hLarge : 327000 * (16 * C) ^ 2 ≤ 2 ^ k := by dsimp [threshold] at hk; omega
  have hPositive : 16 * C < 2 ^ k := by dsimp [threshold] at hk; omega
  have hk0 : k ≠ 0 := by intro h; simp [h] at hq
  have hExcess := scaled_lower_forces_excess C k hC hk0 (hLower (2 ^ k) hN)
  refine ⟨hExcess, ?_⟩
  intro G hFree hEdges
  have hNoCheap (v w) (hvw : v ≠ w) (hNonedge : ¬G.Adj v w) :
      2 ^ k ≤ C * (withEdge G v w hvw).copyCount (cycleGraph 4) := by
    have hAdded := withEdge_edge_count G v w hvw hNonedge
    have hCount := hLower (2 ^ k) hN (withEdge G v w hvw) (by omega)
    simpa only [fourCycleCopies_eq_copyCount] using hCount
  have hExcessThree : 3 ≤ abovePlaneExcess (2 ^ k) := by
    by_contra h
    have hSmall : abovePlaneExcess (2 ^ k) ≤ 2 := by omega
    have hSquare : abovePlaneExcess (2 ^ k) ^ 2 ≤ 4 := by nlinarith
    have hProduct := Nat.mul_le_mul_left (4 * C) hSquare
    nlinarith
  have hDense := extremal_density_of_excess (2 ^ k) G hEdges hExcessThree
  have hPrep := degree_preparation_of_no_cheap_edge (2 ^ k) C hC hq hLarge G hFree hDense hNoCheap
  exact ⟨hNoCheap, hPrep⟩

/-- The claimed square-root bound forces a uniform low-neighbor density at every sufficiently deficient vertex. -/
theorem claimedBound_uniform_large_deficiency_neighbors (hBound : ClaimedBound) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ N : ℕ, ∀ r : ℕ, N ≤ 2 ^ r →
      ∀ G : SimpleGraph (Fin ((2 ^ r) ^ 2 + 2 ^ r + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ r) ^ 2 + 2 ^ r + 2) (cycleGraph 4) →
        ∀ l, 1601 * (8 * (C : ℤ)) ^ 2 * (2611456 * C + 1) ≤ signedDeficiency (2 ^ r) G l →
          ((2 ^ r : ℕ) : ℤ) < 240 * (8 * (C : ℤ)) ^ 2 * (lowNeighbors (2 ^ r) G l).card := by
  obtain ⟨C, hC, N, hPrep⟩ := claimedBound_uniform_preparation hBound
  let cutoff := N + 32 * C + 2611456 * C + 16 * C + 1
  refine ⟨C, hC, cutoff, ?_⟩
  intro r hr G hFree hEdges l hLarge
  have hN : N ≤ 2 ^ r := by dsimp [cutoff] at hr; omega
  have hQ : 32 * C ≤ 2 ^ r := by dsimp [cutoff] at hr; omega
  have hQHigh : 2611456 * C ≤ 2 ^ r := by dsimp [cutoff] at hr; omega
  have hExcessBig : 16 * C < 2 ^ r := by dsimp [cutoff] at hr; omega
  obtain ⟨hExcess, hGraphs⟩ := hPrep r hN
  obtain ⟨hNoCheap, _hMin, hDegree, hHigh, _hPositive⟩ := hGraphs G hFree hEdges
  have hExcessThree : 3 ≤ abovePlaneExcess (2 ^ r) := by
    by_contra h
    have hSmall : abovePlaneExcess (2 ^ r) ≤ 2 := by omega
    have hSquare : abovePlaneExcess (2 ^ r) ^ 2 ≤ 4 := by nlinarith
    have hProduct := Nat.mul_le_mul_left (4 * C) hSquare
    nlinarith
  have hDense := extremal_density_of_excess (2 ^ r) G hEdges hExcessThree
  have hHighQ : (highVertices (2 ^ r) G).card ≤ 2 ^ r := hHigh.trans hQHigh
  have hHighInt : ((highVertices (2 ^ r) G).card : ℤ) ≤ 2611456 * C := by exact_mod_cast hHigh
  have hThreshold := mul_le_mul_of_nonneg_left (add_le_add_right hHighInt 1)
    (show 0 ≤ 1601 * (8 * (C : ℤ)) ^ 2 by positivity)
  have hLargeActual : 1601 * (8 * (C : ℤ)) ^ 2 * ((highVertices (2 ^ r) G).card + 1) ≤
      signedDeficiency (2 ^ r) G l := by
    calc
      _ ≤ 1601 * (8 * (C : ℤ)) ^ 2 * (2611456 * C + 1) := by
        simpa only [add_comm] using hThreshold
      _ ≤ _ := hLarge
  exact growing_deficiency_forces_low_neighbors (2 ^ r) C hC G hFree hDegree hDense
    hQ hHighQ hNoCheap l hLargeActual


/-- A fixed upper bound for the local scale gives a fixed bound on active neighbors. -/
theorem active_neighbors_of_upper_scale (q C K T D₀ : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (hOutside : ∀ v, v ∉ lowHubs q T G → signedDeficiency q G v ≤ K)
    (hScale : 400 * (8 * C) * (K + (highVertices q G).card + 3) ^ 3 ≤ D₀)
    (hT : 16 * D₀ * (K + 1) ≤ T) (hq : 16 * D₀ ≤ q)
    (hSize : 16 * (K + 4) ^ 2 * (16 * D₀) ^ 3 ≤ q)
    (hOverlapT : 24 * (2 * D₀) ^ 2 * K ≤ T)
    (hOverlapQ : 12 * (2 * D₀) ^ 2 * (2 + K ^ 2) ≤ q) (x : Fin (q ^ 2 + q + 2)) :
    (G.neighborFinset x ∩ activeLowVertices q T G).card ≤ 18 * (2 * D₀) ^ 2 := by
  let D := 400 * (8 * C) * (K + (highVertices q G).card + 3) ^ 3
  have hDD : D ≤ D₀ := hScale
  have hEq : (D : ℤ) = 400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3 := by
    simp [D]
  have hTActual : 16 * D * (K + 1) ≤ T := by
    calc
      _ ≤ 16 * D₀ * (K + 1) := by gcongr
      _ ≤ _ := hT
  have hqActual : 16 * D ≤ q := (Nat.mul_le_mul_left 16 hDD).trans hq
  have hSizeActual : 16 * (K + 4) ^ 2 * (16 * D) ^ 3 ≤ q := by
    calc
      _ ≤ 16 * (K + 4) ^ 2 * (16 * D₀) ^ 3 := by gcongr
      _ ≤ _ := hSize
  have hOverlapTActual : 24 * (2 * D) ^ 2 * K ≤ T := by
    calc
      _ ≤ 24 * (2 * D₀) ^ 2 * K := by gcongr
      _ ≤ _ := hOverlapT
  have hOverlapQActual : 12 * (2 * D) ^ 2 * (2 + K ^ 2) ≤ q := by
    calc
      _ ≤ 12 * (2 * D₀) ^ 2 * (2 + K ^ 2) := by gcongr
      _ ≤ _ := hOverlapQ
  have hCount := activeLowVertices_neighbor_card_le q C K T hC hK hKq G hFree hDegree hDense hHigh
    hNoCheap hOutside D hEq (by exact_mod_cast hTActual) (by exact_mod_cast hqActual)
    (by exact_mod_cast hSizeActual) (by exact_mod_cast hOverlapTActual) (by exact_mod_cast hOverlapQActual) x
  have hCountNat : (G.neighborFinset x ∩ activeLowVertices q T G).card ≤ 18 * (2 * D) ^ 2 := by
    exact_mod_cast hCount
  exact hCountNat.trans (by gcongr)

/-- The claimed square-root bound forces a fixed upper bound on all deficiencies of large dyadic extremizers. -/
theorem claimedBound_uniform_bounded_deficiency (hBound : ClaimedBound) :
    ∃ K₁ : ℕ, 1 ≤ K₁ ∧ ∃ N₁ : ℕ, ∀ r : ℕ, N₁ ≤ 2 ^ r →
      ∀ G : SimpleGraph (Fin ((2 ^ r) ^ 2 + 2 ^ r + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ r) ^ 2 + 2 ^ r + 2) (cycleGraph 4) →
        ∀ v, signedDeficiency (2 ^ r) G v ≤ K₁ := by
  obtain ⟨C, hC, N, hPrep⟩ := claimedBound_uniform_preparation hBound
  let H := 2611456 * C
  let R := 16 * C
  let K := 1601 * (8 * C) ^ 2 * (H + 1) + 1
  let D := 400 * (8 * C) * (K + H + 3) ^ 3
  let T := 1 + 240 * (8 * C) ^ 2 + 16 * D * (K + 1) +
    24 * (2 * D) ^ 2 * K + 8 * (K + 1)
  let U := 18 * T ^ 2
  let A := 18 * (2 * D) ^ 2
  let M := 2 * U + A
  let J := 18 * (2 * R) ^ 2 + U ^ 2
  let B := 17 + J + H + (K + 1) * M
  let F := M + H + J + U
  let Q := 2 * B * (4 * B + 1) + J
  let B₁ := 17 + (K + 1) * (10 * R) + H
  let cap₀ := 16 * C * (3 * M + 4 * B + 3 * H + J + 3)
  let cap₁ := 16 * C * (3 * M + 4 * B₁ + 3 * H + J + 3)
  let cap₂ := 10 * R + 5 * H + U + Q + 10
  let K₁ := cap₀ + cap₁ + cap₂ + 1
  let cutoff := N + H + K + 48 * C + 2 + 16 * D +
    16 * (K + 4) ^ 2 * (16 * D) ^ 3 + 12 * (2 * D) ^ 2 * (2 + K ^ 2) +
    6 * T ^ 2 + 4 * (2 * H + 33) + 2 * R * (M + H + K * M + 18) +
    6 * (2 * R) ^ 2 + (K + F + 2 * M + 1) + (8 * C * (F + 2 * M + 1) + 1) +
    2 * R * (3 * U + H) + 8 * (10 * R) + 8 * (H + 1)
  refine ⟨K₁, by dsimp only [K₁]; omega, cutoff, ?_⟩
  intro r hr G hFree hEdges
  let q := 2 ^ r
  have hCutoff : cutoff ≤ q := hr
  have hN : N ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHq : H ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hKq : K ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have h48 : 48 * C ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hqTwo : 2 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have h16D : 16 * D ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hSize : 16 * (K + 4) ^ 2 * (16 * D) ^ 3 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hOverlapQ : 12 * (2 * D) ^ 2 * (2 + K ^ 2) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHubOrder : 6 * T ^ 2 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hLightOrder : 4 * (2 * H + 33) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hJOrder : 2 * R * (M + H + K * M + 18) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hJFamily : 6 * (2 * R) ^ 2 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hPropCount : K + F + 2 * M + 1 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hPropOrder : 8 * C * (F + 2 * M + 1) < q := by dsimp only [cutoff] at hCutoff; omega
  have hSelect : 2 * R * (3 * U + H) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hFew : 8 * (10 * R) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHighOrder : 8 * (H + 1) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hK : 1 ≤ K := by dsimp only [K]; omega
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hT : 1 ≤ T := by dsimp only [T]; omega
  have hTGrow : 240 * (8 * C) ^ 2 ≤ T := by dsimp only [T]; omega
  have hTScale : 16 * D * (K + 1) ≤ T := by dsimp only [T]; omega
  have hTOverlap : 24 * (2 * D) ^ 2 * K ≤ T := by dsimp only [T]; omega
  have hTLight : 8 * (K + 1) ≤ T := by dsimp only [T]; omega
  have hT8 : 8 ≤ T := by omega
  obtain ⟨hExcess, hGraphs⟩ := hPrep r hN
  obtain ⟨hNoCheap, hMin, hDegree, hHigh, _hPositive⟩ := hGraphs G hFree hEdges
  change q ≤ 4 * C * abovePlaneExcess q ^ 2 at hExcess
  change (∀ v, q ≤ R * G.degree v) at hMin
  change (∀ v, G.degree v ≤ q + 2) at hDegree
  change (highVertices q G).card ≤ H at hHigh
  have hHighQ : (highVertices q G).card ≤ q := hHigh.trans hHq
  have hExcessThree : 3 ≤ abovePlaneExcess q := by
    by_contra h
    have hSmall : abovePlaneExcess q ≤ 2 := by omega
    have hSquare : abovePlaneExcess q ^ 2 ≤ 4 := by nlinarith only [hSmall]
    have hProduct := Nat.mul_le_mul_left (4 * C) hSquare
    omega
  have hDense := extremal_density_of_excess q G hEdges hExcessThree
  have hLowSize := dense_lowVertices_card_le q G hDegree hDense hHighQ
  have hPositiveTotal := dense_positiveDeficiency_le_high_card q G hDegree hDense
  have hHighInt : ((highVertices q G).card : ℤ) ≤ q := by exact_mod_cast hHighQ
  have hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ) :=
    hPositiveTotal.trans (by omega)
  have hKActual : 1601 * (8 * C) ^ 2 * ((highVertices q G).card + 1) ≤ K := by
    calc
      _ ≤ 1601 * (8 * C) ^ 2 * (H + 1) := by gcongr
      _ ≤ _ := by dsimp only [K]; omega
  have hOutside (v) (hv : v ∉ lowHubs q T G) : signedDeficiency q G v ≤ K :=
    growing_deficiency_le_off_lowHubs q C T K hC G hFree hDegree hDense (by omega) hHighQ hNoCheap
      (by exact_mod_cast hTGrow) (by exact_mod_cast hKActual) v hv
  have hScale : 400 * (8 * C) * (K + (highVertices q G).card + 3) ^ 3 ≤ D := by
    dsimp only [D]
    gcongr
  have hHubCount : (lowHubs q T G).card ≤ U := by
    have h := lowHubs_card_le q T hT hHubOrder G hFree hLowSize
    dsimp only [U]
    exact_mod_cast h
  have hActive (v) : (G.neighborFinset v ∩ activeLowVertices q T G).card ≤ A := by
    exact active_neighbors_of_upper_scale q C K T D hC hK hKq G hFree hDegree hDense hHighQ
      hNoCheap hOutside hScale hTScale h16D hSize hTOverlap hOverlapQ v
  have hNonlight (v) (hv : v ∉ lowHubs q T G) :
      (G.neighborFinset v ∩ nonlightLowVertices q T G).card ≤ M := by
    have h := nonlight_neighbor_card_le q T G hFree v hv A (by exact_mod_cast hActive v)
    have hU : ((lowHubs q T G).card : ℤ) ≤ U := by exact_mod_cast hHubCount
    have hBound : ((G.neighborFinset v ∩ nonlightLowVertices q T G).card : ℤ) ≤ 2 * U + A := by omega
    dsimp only [M]
    exact_mod_cast hBound
  have hLightHigh : 4 * (2 * ((highVertices q G).card : ℤ) + 33) ≤ q := by
    have h : 4 * (2 * (highVertices q G).card + 33) ≤ q := by omega
    exact_mod_cast h
  have hIndependent := lightLowVertices_independent q T (by omega) K (by positivity)
    G hFree hOutside (by exact_mod_cast hTLight) hTotal hLightHigh
  have hLightDegree (v) (hv : v ∈ lightLowVertices q T G) : (lowNeighbors q G v).card ≤ M := by
    have hNotClosure := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
    have hNotHub : v ∉ lowHubs q T G := fun h => hNotClosure (Finset.mem_union_left _ h)
    rw [light_lowNeighbors_eq_nonlight q T G hIndependent v hv]
    exact hNonlight v hNotHub
  have hTriangles (v) (hv : v ∈ lightLowVertices q T G) : (triangularRegularNeighbors q G v).card ≤ 16 := by
    obtain ⟨hvOutside, hUnit, hLight⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvLow, hvNot⟩ := Finset.mem_sdiff.mp hvOutside
    have hFew := (outside_lowHubClosure_bounds q T K G hOutside v hvLow hvNot).2.2
    have hT8Int : (8 : ℤ) ≤ T := by exact_mod_cast hT8
    have hFewScale := mul_le_mul_of_nonneg_right hT8Int (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G v).card)
    have hFew8 : 8 * ((lowNeighbors q G v).card : ℤ) ≤ q := by omega
    have hHigh8 : 8 * (((highVertices q G).card : ℤ) + 1) ≤ q := by
      have h : 8 * ((highVertices q G).card + 1) ≤ q := by omega
      exact_mod_cast h
    exact light_unit_triangle_bound q (by omega) G hFree v hUnit hFew8 hHigh8 hTotal (by omega)
  have hJOrderActual : 2 * (R : ℤ) * ((M : ℤ) + (highVertices q G).card + (K : ℤ) * M + 18) ≤ q := by
    have h : 2 * R * (M + (highVertices q G).card + K * M + 18) ≤ q := by
      calc
        _ ≤ 2 * R * (M + H + K * M + 18) := by gcongr
        _ ≤ _ := hJOrder
    exact_mod_cast h
  have hJRaw := lightTriangleRegularVertices_card_le q T R hR G hFree K M M (by positivity)
    hOutside hMin (fun v hv => by exact_mod_cast hLightDegree v hv) hTriangles
    (fun v hv => by exact_mod_cast hNonlight v hv) hLowSize hJOrderActual (by exact_mod_cast hJFamily)
  have hChoose : (lowHubs q T G).card.choose 2 ≤ U ^ 2 :=
    (Nat.choose_le_pow _ _).trans (by gcongr)
  have hJNat : (lightTriangleRegularVertices q T G).card ≤
      18 * (2 * R) ^ 2 + (lowHubs q T G).card.choose 2 := by exact_mod_cast hJRaw
  have hJCount : (lightTriangleRegularVertices q T G).card ≤ J := by dsimp only [J]; omega
  have hActualF : M + (highVertices q G).card + (lightTriangleRegularVertices q T G).card +
      (lowHubs q T G).card ≤ F := by dsimp only [F]; omega
  have hCountActual : K + (M + (highVertices q G).card + (lightTriangleRegularVertices q T G).card +
      (lowHubs q T G).card) + 2 * M + 1 ≤ q := by omega
  have hOrderActual : 8 * C * (M + (highVertices q G).card + (lightTriangleRegularVertices q T G).card +
      (lowHubs q T G).card + 2 * M + 1) < q := by
    calc
      _ ≤ 8 * C * (F + 2 * M + 1) := by gcongr
      _ < _ := hPropOrder
  have hGood (v) (hvLow : 1 ≤ signedDeficiency q G v) (hvNot : v ∉ lowHubs q T G) :
      (regularPositivePartners q G v).card ≤ Q := by
    let Bg := 17 + (lightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M
    have hBg : Bg ≤ B := by dsimp only [Bg, B]; omega
    have hFiltered := low_positive_regular_light_bound q C T K M G hFree hOutside hIndependent hTriangles
      hNonlight v hvLow hvNot hCountActual hOrderActual hNoCheap
    change ((positivePartners q G v).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ lightLowVertices q T G).card ≤
      2 * Bg * (4 * Bg + 1) + (lightTriangleRegularVertices q T G).card at hFiltered
    have hUpper : 2 * Bg * (4 * Bg + 1) + (lightTriangleRegularVertices q T G).card ≤ Q := by
      dsimp only [Q]
      gcongr
    have hSubset : regularPositivePartners q G v ⊆
        (positivePartners q G v).filter (fun y => signedDeficiency q G y = 0 ∨ y ∈ lightLowVertices q T G) := by
      intro y hy
      obtain ⟨hyP, hyRegular⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyP, Or.inl hyRegular⟩
    exact (Finset.card_le_card hSubset).trans (hFiltered.trans hUpper)
  have hBActual : 1 + (lightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M ≤ B := by
    dsimp only [B]
    omega
  have hB₁Actual : 17 + (K + 1) * (10 * R) + (highVertices q G).card ≤ B₁ := by dsimp only [B₁]; omega
  have hSelectActual : 2 * (R : ℤ) * (3 * (lowHubs q T G).card + (highVertices q G).card) ≤ q := by
    have h : 2 * R * (3 * (lowHubs q T G).card + (highVertices q G).card) ≤ q := by
      calc
        _ ≤ 2 * R * (3 * U + H) := by gcongr
        _ ≤ _ := hSelect
    exact_mod_cast h
  have hHighOrderActual : 8 * ((highVertices q G).card + 1) ≤ q := by omega
  intro v
  have hGlobal := signedDeficiency_bounded_of_structure q C T K M R B B₁ Q hC hR h48 hqTwo G hFree hDegree
    hDense hHighQ hMin hIndependent hOutside hNonlight hGood hBActual hB₁Actual hSelectActual hFew
    hHighOrderActual hNoCheap v
  have hCap₀ : 16 * (C : ℤ) * (3 * M + 4 * B + 3 * (highVertices q G).card +
      (lightTriangleRegularVertices q T G).card + 3) ≤ cap₀ := by
    have h : 16 * C * (3 * M + 4 * B + 3 * (highVertices q G).card +
        (lightTriangleRegularVertices q T G).card + 3) ≤ cap₀ := by
      dsimp only [cap₀]
      gcongr
    exact_mod_cast h
  have hCap₁ : 16 * (C : ℤ) * (3 * M + 4 * B₁ + 3 * (highVertices q G).card +
      (lightTriangleRegularVertices q T G).card + 3) ≤ cap₁ := by
    have h : 16 * C * (3 * M + 4 * B₁ + 3 * (highVertices q G).card +
        (lightTriangleRegularVertices q T G).card + 3) ≤ cap₁ := by
      dsimp only [cap₁]
      gcongr
    exact_mod_cast h
  have hCap₂ : (10 : ℤ) * R + 5 * (highVertices q G).card + (lowHubs q T G).card + Q + 10 ≤ cap₂ := by
    have h : 10 * R + 5 * (highVertices q G).card + (lowHubs q T G).card + Q + 10 ≤ cap₂ := by
      dsimp only [cap₂]
      omega
    exact_mod_cast h
  have hCap₀K : (cap₀ : ℤ) ≤ K₁ := by exact_mod_cast (show cap₀ ≤ K₁ by dsimp only [K₁]; omega)
  have hCap₁K : (cap₁ : ℤ) ≤ K₁ := by exact_mod_cast (show cap₁ ≤ K₁ by dsimp only [K₁]; omega)
  have hCap₂K : (cap₂ : ℤ) ≤ K₁ := by exact_mod_cast (show cap₂ ≤ K₁ by dsimp only [K₁]; omega)
  exact hGlobal.trans (max_le (max_le (hCap₀.trans hCap₀K) (hCap₁.trans hCap₁K)) (hCap₂.trans hCap₂K))

/- Bounded-deficiency light structure and common zero-codegree neighborhoods. -/
section

/-- A global deficiency bound controls the positive weight in every neighborhood. -/
theorem neighbor_positive_weight_global {n : ℕ} (q : ℕ) (K : ℤ)
    (G : SimpleGraph (Fin n)) (hBound : ∀ v, signedDeficiency q G v ≤ K) (v : Fin n) :
    (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤
      K * (lowNeighbors q G v).card := by
  have hSum := Finset.sum_le_sum (fun w (_ : w ∈ lowNeighbors q G v) => hBound w)
  rw [sum_lowNeighbors_deficiency] at hSum
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hSum

/-- Outside the hub set, the bounded branch has both a small low degree and a bounded neighboring weight. -/
theorem bounded_outside_lowHubs_bounds {n : ℕ} (q T : ℕ) (K : ℤ)
    (G : SimpleGraph (Fin n)) (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (l : Fin n) (hLow : l ∈ lowVertices q G) (hl : l ∉ lowHubs q T G) :
    signedDeficiency q G l ≤ K ∧
      (∑ w ∈ G.neighborFinset l, positiveDeficiency q G w) ≤ K * (lowNeighbors q G l).card ∧
      T * ((lowNeighbors q G l).card : ℤ) < q := by
  refine ⟨hBound l, neighbor_positive_weight_global q K G hBound l, ?_⟩
  by_contra h
  exact hl (Finset.mem_filter.mpr ⟨hLow, by omega⟩)

/-- The bounded branch excludes the hubs themselves when selecting light lows. -/
def boundedLightLowVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (lowVertices q G \ lowHubs q T G).filter fun v =>
    signedDeficiency q G v = 1 ∧ 2 * ((triangularRegularNeighbors q G v).card : ℤ) < q

def boundedActiveLowVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (lowVertices q G \ lowHubs q T G).filter fun v =>
    2 ≤ signedDeficiency q G v ∨ (q : ℤ) ≤ 2 * (triangularRegularNeighbors q G v).card

def boundedNonlightLowVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  lowVertices q G \ boundedLightLowVertices q T G

theorem boundedLightLowVertices_independent (q T : ℕ) (hq : 0 < q) (K : ℤ) (hK : 0 ≤ K)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (hT : 8 * (K + 1) ≤ T)
    (hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * q)
    (hHigh : 4 * (2 * ((highVertices q G).card : ℤ) + 33) ≤ q) :
    ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w := by
  have hSpec (v) (hv : v ∈ boundedLightLowVertices q T G) :
      signedDeficiency q G v = 1 ∧
      (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ K * (lowNeighbors q G v).card ∧
      8 * (K + 1) * (lowNeighbors q G v).card ≤ (q : ℤ) ∧
      (triangularRegularNeighbors q G v).card ≤ 16 := by
    obtain ⟨hvOutside, hvUnit, hvLight⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvLow, hvNot⟩ := Finset.mem_sdiff.mp hvOutside
    obtain ⟨_, hWeight, hFew⟩ := bounded_outside_lowHubs_bounds q T K G hBound v hvLow hvNot
    have hFewScaled := mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G v).card)
    have hFewFinal : 8 * (K + 1) * (lowNeighbors q G v).card ≤ (q : ℤ) := by omega
    have hBasic : 8 * ((lowNeighbors q G v).card : ℤ) ≤ (q : ℤ) := by
      have hExtra := mul_nonneg hK (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G v).card)
      nlinarith only [hFewFinal, hExtra]
    have hHighBasic : 8 * (((highVertices q G).card : ℤ) + 1) ≤ (q : ℤ) := by omega
    have hTriangles := light_unit_triangle_bound q hq G hFree v hvUnit hBasic hHighBasic hTotal (by omega)
    exact ⟨hvUnit, hWeight, hFewFinal, hTriangles⟩
  exact light_unit_set_independent q hq G hFree (boundedLightLowVertices q T G) K hK
    (fun v hv => (hSpec v hv).1) (fun v hv => (hSpec v hv).2.2.2)
    (fun v hv => (hSpec v hv).2.1) (fun v hv => (hSpec v hv).2.2.1) hHigh

theorem bounded_active_low_many_partners (q C K T : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (D : ℤ) (hD : D = 400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3)
    (hT : 16 * D * ((K : ℤ) + 1) ≤ T) (hq : 16 * D ≤ q)
    (hSize : 16 * ((K : ℤ) + 4) ^ 2 * (16 * D) ^ 3 ≤ q)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ boundedActiveLowVertices q T G) :
    (q : ℤ) ≤ 2 * D * (lowPositivePartners q G v).card := by
  obtain ⟨hvOutside, hvActive⟩ := Finset.mem_filter.mp hv
  obtain ⟨hvLow, hvNot⟩ := Finset.mem_sdiff.mp hvOutside
  have hLow : 1 ≤ signedDeficiency q G v := by
    have h := (Finset.mem_filter.mp hvLow).2
    omega
  obtain ⟨hBound, hWeight, hFew⟩ := bounded_outside_lowHubs_bounds q T K G hBound v hvLow hvNot
  have hKInt : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
  have hDPos : 0 < D := by rw [hD]; positivity
  have hDelta : (0 : ℤ) ≤ (lowNeighbors q G v).card := by positivity
  have hc : 0 ≤ ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w :=
    Finset.sum_nonneg (fun w _ => positiveDeficiency_nonnegative q G w)
  have hWeightScaled := mul_le_mul_of_nonneg_left hWeight (show 0 ≤ 16 * D by omega)
  have hThresholdScaled := mul_le_mul_of_nonneg_right hT hDelta
  have hLocalSmall : 16 * D * ((∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) +
      (lowNeighbors q G v).card) ≤ (q : ℤ) := by
    nlinarith only [hWeightScaled, hThresholdScaled, hFew]
  have hSparse : 8 * D * (1 + (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) +
      (lowNeighbors q G v).card) ≤ (q : ℤ) := by nlinarith only [hLocalSmall, hq]
  have hNeighborWeight : (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ (q : ℤ) := by
    have hExtra := mul_nonneg (show 0 ≤ 16 * D - 1 by omega) hc
    have hDeltaExtra := mul_nonneg (show 0 ≤ 16 * D by omega) hDelta
    nlinarith only [hLocalSmall, hExtra, hDeltaExtra]
  have hResult := bounded_deficiency_many_low_partners q C K hC hK hKq G hFree hDegree hDense
    hHigh hNoCheap v hLow hBound hNeighborWeight hvActive
    (by simpa only [hD] using hSparse) (by simpa only [hD] using hSize)
  simpa only [hD] using hResult

theorem boundedActiveLowVertices_neighbor_card_le (q C K T : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (D : ℤ) (hD : D = 400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3)
    (hT : 16 * D * ((K : ℤ) + 1) ≤ T) (hq : 16 * D ≤ q)
    (hSize : 16 * ((K : ℤ) + 4) ^ 2 * (16 * D) ^ 3 ≤ q)
    (hOverlapT : 24 * (2 * D) ^ 2 * K ≤ T)
    (hOverlapQ : 12 * (2 * D) ^ 2 * (2 + (K : ℤ) ^ 2) ≤ q)
    (x : Fin (q ^ 2 + q + 2)) :
    ((G.neighborFinset x ∩ boundedActiveLowVertices q T G).card : ℤ) ≤ 18 * (2 * D) ^ 2 := by
  let A := G.neighborFinset x ∩ boundedActiveLowVertices q T G
  let B := 2 * D
  let J := (K : ℤ) * q / T
  have hKInt : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hCInt : (1 : ℤ) ≤ C := by exact_mod_cast hC
  have hDPos : 0 < D := by rw [hD]; positivity
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hTPos : (0 : ℤ) < T := by
    have hPositive : 0 < 16 * D * ((K : ℤ) + 1) := by positivity
    omega
  have hJ : 0 ≤ J := Int.ediv_nonneg (by positivity) (le_of_lt hTPos)
  have hqNat : 0 < q := by omega
  have hLow (v) (hv : v ∈ A) : 1 ≤ signedDeficiency q G v := by
    have h := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).1).1
    have hPositive := (Finset.mem_filter.mp h).2
    omega
  have hSpec (v) (hv : v ∈ A) : signedDeficiency q G v ≤ K ∧
      (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤ J := by
    have hvAct := (Finset.mem_inter.mp hv).2
    have hvLow := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvAct).1).1
    have hvNot := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvAct).1).2
    obtain ⟨hBound, hWeight, hFew⟩ := bounded_outside_lowHubs_bounds q T K G hBound v hvLow hvNot
    refine ⟨hBound, ?_⟩
    apply (Int.le_ediv_iff_mul_le hTPos).mpr
    have h1 := mul_le_mul_of_nonneg_left hWeight (le_of_lt hTPos)
    have h2 := mul_le_mul_of_nonneg_left hFew.le (show 0 ≤ (K : ℤ) by omega)
    nlinarith only [h1, h2]
  have hLarge (v) (hv : v ∈ A) : (q : ℤ) ≤ B * (lowPositivePartners q G v).card :=
    bounded_active_low_many_partners q C K T hC hK hKq G hFree hDegree hDense hHigh hNoCheap
      hBound D hD hT hq hSize v (Finset.mem_inter.mp hv).2
  have hTJ : (T : ℤ) * J ≤ (K : ℤ) * q := Int.mul_ediv_self_le (ne_of_gt hTPos)
  have hOverlapScaled := mul_le_mul_of_nonneg_right hOverlapT hJ
  have hVariable : 24 * B ^ 2 * J ≤ (q : ℤ) := by
    apply (mul_le_mul_iff_of_pos_left (show (0 : ℤ) < K by omega)).mp
    dsimp only [B]
    linear_combination hTJ + hOverlapScaled
  have hGap : 6 * B ^ 2 * (2 + (K : ℤ) ^ 2 + 2 * J) ≤ (q : ℤ) := by
    change 12 * B ^ 2 * (2 + (K : ℤ) ^ 2) ≤ (q : ℤ) at hOverlapQ
    nlinarith only [hVariable, hOverlapQ]
  exact large_low_partner_neighbors_card_le q G hFree hDegree x A Finset.inter_subset_left K J B hKInt hJ hB
    hqNat hLow (fun v hv => (hSpec v hv).1) (fun v hv => (hSpec v hv).2) hLarge
    (dense_lowVertices_card_le q G hDegree hDense hHigh) hGap

theorem boundedNonlightLowVertices_subset {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) :
    boundedNonlightLowVertices q T G ⊆ lowHubs q T G ∪ boundedActiveLowVertices q T G := by
  intro v hv
  obtain ⟨hvLow, hvNotLight⟩ := Finset.mem_sdiff.mp hv
  by_cases hvClosure : v ∈ lowHubs q T G
  · exact Finset.mem_union_left _ hvClosure
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hvLow, hvClosure⟩, ?_⟩
    have hPositive := (Finset.mem_filter.mp hvLow).2
    by_cases hUnit : signedDeficiency q G v = 1
    · apply Or.inr
      by_contra h
      exact hvNotLight (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvLow, hvClosure⟩, hUnit, by omega⟩)
    · exact Or.inl (by omega)

/-- Every vertex has a bounded number of nonlight low neighbors in the bounded branch. -/
theorem bounded_nonlight_neighbor_card_le {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) (B : ℤ)
    (hActive : ((G.neighborFinset v ∩ boundedActiveLowVertices q T G).card : ℤ) ≤ B) :
    ((G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤
      (lowHubs q T G).card + B := by
  have hCover : G.neighborFinset v ∩ boundedNonlightLowVertices q T G ⊆
      lowHubs q T G ∪ (G.neighborFinset v ∩ boundedActiveLowVertices q T G) := by
    intro w hw
    obtain ⟨hwN, hwNonlight⟩ := Finset.mem_inter.mp hw
    rcases Finset.mem_union.mp (boundedNonlightLowVertices_subset q T G hwNonlight) with hwU | hwA
    · exact Finset.mem_union_left _ hwU
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hwN, hwA⟩)
  have hCard := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hInt : ((G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤
      (lowHubs q T G).card + (G.neighborFinset v ∩ boundedActiveLowVertices q T G).card := by
    exact_mod_cast hCard
  omega

theorem bounded_light_lowNeighbors_eq_nonlight {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (l : Fin n) (hl : l ∈ boundedLightLowVertices q T G) :
    lowNeighbors q G l = G.neighborFinset l ∩ boundedNonlightLowVertices q T G := by
  rw [lowNeighbors_eq_inter]
  ext w
  simp only [Finset.mem_inter, boundedNonlightLowVertices, Finset.mem_sdiff]
  constructor
  · rintro ⟨hwN, hwLow⟩
    refine ⟨hwN, hwLow, ?_⟩
    intro hwLight
    exact hIndependent l hl w hwLight ((G.mem_neighborFinset l w).mp hwN)
  · rintro ⟨hwN, hwLow, _⟩
    exact ⟨hwN, hwLow⟩

theorem bounded_light_positivePartners_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (K M : ℤ) (hK : 0 ≤ K) (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G,
      ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (l : Fin (q ^ 2 + q + 2)) (hl : l ∈ boundedLightLowVertices q T G)
    (hTriangles : (triangularRegularNeighbors q G l).card ≤ 16)
    (hNonlight : ((G.neighborFinset l ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤ M) :
    ((positivePartners q G l).card : ℤ) ≤ 17 + (K + 1) * M + (highVertices q G).card := by
  have hUnit := (Finset.mem_filter.mp hl).2.1
  have hWeight := neighbor_positive_weight_global q K G hBound l
  have hRow := unit_positivePartners_card_le q G hFree l hUnit hTriangles K hWeight
  have hDegree : ((lowNeighbors q G l).card : ℤ) ≤ M := by
    rw [bounded_light_lowNeighbors_eq_nonlight q T G hIndependent l hl]
    exact hNonlight
  have hScaled := mul_le_mul_of_nonneg_left hDegree (show 0 ≤ K + 1 by omega)
  omega

def boundedLightTriangleRegularVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (boundedLightLowVertices q T G).biUnion (fun l => triangularRegularNeighbors q G l)

theorem bounded_light_triangle_neighbor_weight_lower (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (d : ℤ) (hLowDegree : ∀ l ∈ boundedLightLowVertices q T G, ((lowNeighbors q G l).card : ℤ) ≤ d)
    (hTriangles : ∀ l ∈ boundedLightLowVertices q T G, (triangularRegularNeighbors q G l).card ≤ 16)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ boundedLightTriangleRegularVertices q T G) :
    (q : ℤ) - d - (highVertices q G).card - 17 ≤
      ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  obtain ⟨l, hl, hlv⟩ := Finset.mem_biUnion.mp hv
  have hUnit := (Finset.mem_filter.mp hl).2.1
  have hDegree : (G.degree l : ℤ) = q := by unfold signedDeficiency at hUnit; omega
  have hRegular := regular_neighbor_card_lower q G l
  rw [hDegree] at hRegular
  have hCover := triangular_regular_neighbor_cover_bound q G hFree l (by omega) v hlv
  have hTri : ((triangularRegularNeighbors q G l).card : ℤ) ≤ 16 := by exact_mod_cast hTriangles l hl
  have hLow := hLowDegree l hl
  omega

/-- The light and nonlight partition bounds neighboring deficiency globally. -/
theorem bounded_neighbor_positive_weight (q T : ℕ) (K : ℤ) (hK : 0 ≤ K)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (v : Fin (q ^ 2 + q + 2)) :
    (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ≤
      (G.neighborFinset v ∩ boundedLightLowVertices q T G).card +
        K * (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card := by
  have hEach (w) (_ : w ∈ G.neighborFinset v) : positiveDeficiency q G w ≤
      (if w ∈ boundedLightLowVertices q T G then (1 : ℤ) else 0) +
        (if w ∈ boundedNonlightLowVertices q T G then K else 0) := by
    by_cases hLight : w ∈ boundedLightLowVertices q T G
    · have hUnit := (Finset.mem_filter.mp hLight).2.1
      have hNot : w ∉ boundedNonlightLowVertices q T G := fun h => (Finset.mem_sdiff.mp h).2 hLight
      simp only [ite_eq_left hLight, ite_eq_right hNot, add_zero]
      simp [positiveDeficiency, hUnit]
    · rw [ite_eq_right hLight, zero_add]
      by_cases hLow : 0 < signedDeficiency q G w
      · have hNonlight : w ∈ boundedNonlightLowVertices q T G := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLow⟩, hLight⟩
        rw [ite_eq_left hNonlight]
        exact max_le (hBound w) hK
      · have hNot : w ∉ boundedNonlightLowVertices q T G := by
          intro h
          exact hLow (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
        rw [ite_eq_right hNot]
        exact max_le (by omega) (by omega)
  have hSum := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib, neighbor_indicator_weight_sum, neighbor_indicator_weight_sum, one_mul] at hSum
  exact hSum

/-- Only boundedly many regular vertices lie on triangular edges to bounded-branch lights. -/
theorem boundedLightTriangleRegularVertices_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (K d M : ℤ) (hK : 0 ≤ K) (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (hLowDegree : ∀ l ∈ boundedLightLowVertices q T G, ((lowNeighbors q G l).card : ℤ) ≤ d)
    (hTriangles : ∀ l ∈ boundedLightLowVertices q T G, (triangularRegularNeighbors q G l).card ≤ 16)
    (hNonlight : ∀ v, ((G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤ M)
    (hSize : ((lowVertices q G).card : ℤ) ≤ 3 * q)
    (hOrder : 2 * (d + (highVertices q G).card + K * M + 17) ≤ q)
    (hFamily : 24 ≤ q) : ((boundedLightTriangleRegularVertices q T G).card : ℤ) ≤ 72 := by
  let J := boundedLightTriangleRegularVertices q T G
  let L := boundedLightLowVertices q T G
  have hLightSize : (L.card : ℤ) ≤ 3 * q := by
    have hSubset : L ⊆ lowVertices q G := by
      intro l hl
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hl).1).1
    exact (show (L.card : ℤ) ≤ (lowVertices q G).card by exact_mod_cast Finset.card_le_card hSubset).trans hSize
  have hMany (v) (hv : v ∈ J) : (q : ℤ) ≤ 2 * (G.neighborFinset v ∩ L).card := by
    have hLower := bounded_light_triangle_neighbor_weight_lower q T G hFree d hLowDegree hTriangles v hv
    have hUpper := bounded_neighbor_positive_weight q T K hK G hBound v
    have hScaled := mul_le_mul_of_nonneg_left (hNonlight v) hK
    dsimp only [L]
    linarith only [hLower, hUpper, hScaled, hOrder]
  apply finite_family_card_le J L (fun v => G.neighborFinset v ∩ L) q 2 1
    (by exact_mod_cast (show 0 < q by omega)) (by norm_num) (by norm_num)
  · intro v _
    exact Finset.inter_subset_right
  · exact hLightSize
  · exact hMany
  · intro v _ w _ hvw
    have hSubset : (G.neighborFinset v ∩ L) ∩ (G.neighborFinset w ∩ L) ⊆
        G.neighborFinset v ∩ G.neighborFinset w := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    have hCard : (((G.neighborFinset v ∩ L) ∩ (G.neighborFinset w ∩ L)).card : ℤ) ≤
        (G.neighborFinset v ∩ G.neighborFinset w).card := by exact_mod_cast Finset.card_le_card hSubset
    have hCommon : ((G.neighborFinset v ∩ G.neighborFinset w).card : ℤ) ≤ 1 := by
      exact_mod_cast codegree_le_one G hFree v w hvw
    exact hCard.trans hCommon
  · norm_num
    exact_mod_cast hFamily

def boundedTriangularLightNeighbors {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v).filter fun l => l ∈ boundedLightLowVertices q T G ∧ codegree G v l = 1

theorem bounded_triangular_light_neighbor_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (v : Fin (q ^ 2 + q + 2)) :
    (boundedTriangularLightNeighbors q T G v).card ≤ (boundedLightTriangleRegularVertices q T G).card +
      (highVertices q G).card + (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card := by
  let S := boundedTriangularLightNeighbors q T G v
  have hThird (l) (hl : l ∈ S) : ∃ z, G.Adj v z ∧ G.Adj l z := by
    have hCodegree := (Finset.mem_filter.mp hl).2.2
    have hPositive : 0 < codegree G v l := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hPositive
    exact ⟨z, (G.mem_neighborFinset v z).mp (Finset.mem_inter.mp hz).1,
      (G.mem_neighborFinset l z).mp (Finset.mem_inter.mp hz).2⟩
  let third := fun l => if hl : l ∈ S then (hThird l hl).choose else v
  have hSpec (l) (hl : l ∈ S) : G.Adj v (third l) ∧ G.Adj l (third l) := by
    dsimp only [third]
    rw [dite_eq_left hl]
    exact (hThird l hl).choose_spec
  let P := boundedLightTriangleRegularVertices q T G ∪ highVertices q G ∪
    (G.neighborFinset v ∩ boundedNonlightLowVertices q T G)
  have hMaps (l) (hl : l ∈ S) : third l ∈ P := by
    have hlLight := (Finset.mem_filter.mp hl).2.1
    have hVL := (G.mem_neighborFinset v l).mp (Finset.mem_filter.mp hl).1
    obtain ⟨hVZ, hLZ⟩ := hSpec l hl
    have hzNotLight : third l ∉ boundedLightLowVertices q T G := fun hz => hIndependent l hlLight (third l) hz hLZ
    by_cases hZero : signedDeficiency q G (third l) = 0
    · have hCodegree := codegree_eq_one_of_common_vertex G hFree l (third l) v hLZ.ne hVL.symm hVZ.symm
      have hzRegular : third l ∈ triangularRegularNeighbors q G l := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset l (third l)).mpr hLZ, hZero⟩, hCodegree⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨l, hlLight, hzRegular⟩))
    · by_cases hPositive : 0 < signedDeficiency q G (third l)
      · have hzNonlight : third l ∈ boundedNonlightLowVertices q T G := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPositive⟩, hzNotLight⟩
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v (third l)).mpr hVZ, hzNonlight⟩)
      · have hzHigh : third l ∈ highVertices q G := (mem_highVertices_iff q G (third l)).mpr (by omega)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hzHigh)
  have hCount : S.card ≤ P.card := by
    apply Finset.card_le_card_of_injOn third hMaps
    intro l hl w hw hEqual
    have hVL := (G.mem_neighborFinset v l).mp (Finset.mem_filter.mp hl).1
    have hVW := (G.mem_neighborFinset v w).mp (Finset.mem_filter.mp hw).1
    have hZL := (hSpec l hl).2.symm
    have hZW := (hSpec w hw).2.symm
    rw [← hEqual] at hZW
    exact common_neighbor_unique G hFree (hSpec l hl).1.ne hVL hZL hVW hZW
  have hUnion := Finset.card_union_le (boundedLightTriangleRegularVertices q T G ∪ highVertices q G)
    (G.neighborFinset v ∩ boundedNonlightLowVertices q T G)
  have hFirst := Finset.card_union_le (boundedLightTriangleRegularVertices q T G) (highVertices q G)
  change S.card ≤ _
  dsimp only [P] at hCount
  omega

theorem bounded_regular_negativeResidualMass_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (v : Fin (q ^ 2 + q + 2)) (hRegular : signedDeficiency q G v = 0) :
    negativeResidualMass q G v ≤ (boundedTriangularLightNeighbors q T G v).card +
      ∑ w ∈ G.neighborFinset v ∩ boundedNonlightLowVertices q T G, positiveDeficiency q G w := by
  have hEach (w) (hw : w ∈ G.neighborFinset v) : max (-weightedResidual q G v w) 0 ≤
      (if w ∈ boundedTriangularLightNeighbors q T G v then (1 : ℤ) else 0) +
        (if w ∈ boundedNonlightLowVertices q T G then positiveDeficiency q G w else 0) := by
    have hAdj := (G.mem_neighborFinset v w).mp hw
    have hRow := weightedResidual_regular_neighbor q G v w hAdj hRegular
    have hCodegree : (codegree G v w : ℤ) ≤ 1 := by exact_mod_cast codegree_le_one G hFree v w hAdj.ne
    by_cases hwLight : w ∈ boundedLightLowVertices q T G
    · have hUnit := (Finset.mem_filter.mp hwLight).2.1
      have hwNotNonlight : w ∉ boundedNonlightLowVertices q T G := fun h => (Finset.mem_sdiff.mp h).2 hwLight
      rw [ite_eq_right hwNotNonlight, add_zero]
      by_cases hTri : codegree G v w = 1
      · have hwTri : w ∈ boundedTriangularLightNeighbors q T G v := Finset.mem_filter.mpr ⟨hw, hwLight, hTri⟩
        rw [ite_eq_left hwTri]
        rw [hUnit, hTri] at hRow
        norm_num at hRow
        rw [hRow]
        norm_num
      · have hZero : codegree G v w = 0 := by omega
        have hwNotTri : w ∉ boundedTriangularLightNeighbors q T G v := by
          intro h
          exact hTri (Finset.mem_filter.mp h).2.2
        rw [ite_eq_right hwNotTri]
        rw [hUnit, hZero] at hRow
        norm_num at hRow
        rw [hRow]
        norm_num
    · have hwNotTri : w ∉ boundedTriangularLightNeighbors q T G v := fun h => hwLight (Finset.mem_filter.mp h).2.1
      rw [ite_eq_right hwNotTri, zero_add]
      by_cases hLow : 0 < signedDeficiency q G w
      · have hwNonlight : w ∈ boundedNonlightLowVertices q T G := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLow⟩, hwLight⟩
        rw [ite_eq_left hwNonlight]
        apply max_le
        · have hPositive : positiveDeficiency q G w = signedDeficiency q G w := max_eq_left (by omega)
          rw [hPositive, hRow]
          omega
        · exact positiveDeficiency_nonnegative q G w
      · have hwNonlight : w ∉ boundedNonlightLowVertices q T G := by
          intro h
          exact hLow (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
        rw [ite_eq_right hwNonlight]
        rw [hRow]
        omega
  have hSum := Finset.sum_le_sum hEach
  rw [Finset.sum_add_distrib, neighbor_indicator_weight_sum] at hSum
  have hSubset : boundedTriangularLightNeighbors q T G v ⊆ G.neighborFinset v := Finset.filter_subset _ _
  rw [Finset.inter_eq_right.mpr hSubset, one_mul] at hSum
  have hFilter : ((G.neighborFinset v).filter fun w => w ∈ boundedNonlightLowVertices q T G) =
      G.neighborFinset v ∩ boundedNonlightLowVertices q T G := by
    ext w
    simp
  rw [← Finset.sum_filter, hFilter] at hSum
  rw [regular_negativeResidualMass_eq_neighbor_sum q G hFree v hRegular]
  exact hSum

theorem bounded_regular_positivePartners_card_bound (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (K : ℤ) (hK : 0 ≤ K)
    (hBound : ∀ w, signedDeficiency q G w ≤ K)
    (v : Fin (q ^ 2 + q + 2)) (hRegular : signedDeficiency q G v = 0)
    (B : ℤ) (hNonlight : ((G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤ B) :
    ((positivePartners q G v).card : ℤ) ≤ 1 + (boundedLightTriangleRegularVertices q T G).card +
      (highVertices q G).card + (K + 1) * B := by
  have hEach (w) (_hw : w ∈ G.neighborFinset v ∩ boundedNonlightLowVertices q T G) : positiveDeficiency q G w ≤ K := by
    apply max_le
    · exact hBound w
    · exact hK
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  have hTriangles : ((boundedTriangularLightNeighbors q T G v).card : ℤ) ≤
      (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card +
        (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card := by
    exact_mod_cast bounded_triangular_light_neighbor_card_le q T G hFree hIndependent v
  have hMass := bounded_regular_negativeResidualMass_le q T G hFree v hRegular
  have hCard := positivePartners_card_le_mass q G v
  rw [positiveResidualMass_balance] at hCard
  have hScaled := mul_le_mul_of_nonneg_left hNonlight (show 0 ≤ K + 1 by omega)
  nlinarith only [hSum, hTriangles, hMass, hCard, hScaled]

theorem boundedLightTriangleRegularVertices_regular {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) (hv : v ∈ boundedLightTriangleRegularVertices q T G) : signedDeficiency q G v = 0 := by
  obtain ⟨l, _, hlv⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hlv).1).2

theorem bounded_regular_negative_entry_support (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (y w : Fin (q ^ 2 + q + 2)) (hY : signedDeficiency q G y = 0)
    (hNotJ : y ∉ boundedLightTriangleRegularVertices q T G) (hNe : w ≠ y)
    (hNegative : weightedResidual q G w y < 0) :
    w ∈ G.neighborFinset y ∩ boundedNonlightLowVertices q T G := by
  have hAdj : G.Adj w y := by
    by_contra h
    have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree w y hNe h
    omega
  have hEntry := weightedResidual_off_diagonal q G w y hNe
  rw [adjMatrix_square_codegree] at hEntry
  simp only [G.adjMatrix_apply, ite_eq_left hAdj, hY, add_zero, one_mul] at hEntry
  have hCodegree : codegree G w y ≤ 1 := codegree_le_one G hFree w y hNe
  have hLow : 0 < signedDeficiency q G w := by omega
  have hNotLight : w ∉ boundedLightLowVertices q T G := by
    intro hLight
    have hUnit := (Finset.mem_filter.mp hLight).2.1
    have hTriangle : codegree G w y = 1 := by omega
    have hRegular : y ∈ triangularRegularNeighbors q G w := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset w y).mpr hAdj, hY⟩, hTriangle⟩
    exact hNotJ (Finset.mem_biUnion.mpr ⟨w, hLight, hRegular⟩)
  exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hAdj.symm,
    Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLow⟩, hNotLight⟩⟩

theorem bounded_light_negative_entry_support (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (y w : Fin (q ^ 2 + q + 2)) (hY : y ∈ boundedLightLowVertices q T G) (hNe : w ≠ y)
    (hNegative : weightedResidual q G w y < 0) :
    w ∈ lowNeighbors q G y ∨ w ∈ boundedLightTriangleRegularVertices q T G := by
  have hAdj : G.Adj w y := by
    by_contra h
    have hNonnegative := weightedResidual_nonadj_nonnegative q G hFree w y hNe h
    omega
  have hUnit := (Finset.mem_filter.mp hY).2.1
  have hEntry := weightedResidual_off_diagonal q G w y hNe
  rw [adjMatrix_square_codegree] at hEntry
  simp only [G.adjMatrix_apply, ite_eq_left hAdj, hUnit, one_mul] at hEntry
  have hCodegree : codegree G w y ≤ 1 := codegree_le_one G hFree w y hNe
  by_cases hLow : 0 < signedDeficiency q G w
  · exact Or.inl (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y w).mpr hAdj.symm, hLow⟩)
  · have hZero : signedDeficiency q G w = 0 := by omega
    have hTriangle : codegree G w y = 1 := by omega
    have hRegular : w ∈ triangularRegularNeighbors q G y := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y w).mpr hAdj.symm, hZero⟩,
        by rw [codegree_symm]; exact hTriangle⟩
    exact Or.inr (Finset.mem_biUnion.mpr ⟨y, hY, hRegular⟩)

theorem bounded_negative_support_column_exceptions (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l y : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (hY : y ∈ positivePartners q G l) (hNonhighY : 0 ≤ signedDeficiency q G y)
    (X S : Finset (Fin (q ^ 2 + q + 2))) (hX : X ⊆ G.neighborFinset l)
    (hNonhighX : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (hNotS : l ∉ S)
    (hSupport : ∀ w, w ≠ y → weightedResidual q G w y < 0 →
      w ∈ S ∨ w ∈ boundedLightTriangleRegularVertices q T G)
    (hAvoid : ∀ x ∈ X, Disjoint (G.neighborFinset x) (boundedLightTriangleRegularVertices q T G)) :
    (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ S.card := by
  obtain ⟨hNe, hNot, hZero⟩ := positivePartner_nonhigh q G l y hLow hNonhighY hY
  have hEntry : weightedResidual q G l y = 1 := by
    rw [weightedResidual_nonadj q G l y hNe hNot, hZero]
    norm_num
  have hSubset : (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1) ⊆
      X.filter (fun x => ∃ w ∈ S, G.Adj x w) := by
    intro x hx
    obtain ⟨hxX, hxBad⟩ := Finset.mem_filter.mp hx
    have hLX := (G.mem_neighborFinset l x).mp (hX hxX)
    have hXYNe : x ≠ y := by intro h; subst x; exact hNot hLX
    have hXYNot : ¬G.Adj x y := by
      intro h
      exact (codegree_eq_zero_iff G l y).mp hZero x hLX h.symm
    have hZXY := weightedResidual_nonadj_nonnegative q G hFree x y hXYNe hXYNot
    obtain ⟨w, hw, hwNegative⟩ := bad_commutator_has_negative_neighbor q G x l y
      ((G.mem_neighborFinset x l).mpr hLX.symm) hEntry (hNonhighX x hxX) hZXY hxBad
    have hXW := (G.mem_neighborFinset x w).mp (Finset.mem_erase.mp hw).2
    have hWYNe : w ≠ y := by intro h; subst w; exact hXYNot hXW
    rcases hSupport w hWYNe hwNegative with hwS | hwJ
    · exact Finset.mem_filter.mpr ⟨hxX, w, hwS, hXW⟩
    · exact False.elim ((Finset.disjoint_left.mp (hAvoid x hxX)) (Finset.mem_erase.mp hw).2 hwJ)
  exact (Finset.card_le_card hSubset).trans (neighbor_hits_set_card_le G hFree l X S hX hNotS)

theorem bounded_regular_or_light_column_exceptions (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l y : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (hY : y ∈ positivePartners q G l)
    (hType : (signedDeficiency q G y = 0 ∧ y ∉ boundedLightTriangleRegularVertices q T G) ∨ y ∈ boundedLightLowVertices q T G)
    (X : Finset (Fin (q ^ 2 + q + 2))) (hX : X ⊆ G.neighborFinset l)
    (hNonhighX : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (hAvoid : ∀ x ∈ X, Disjoint (G.neighborFinset x) (boundedLightTriangleRegularVertices q T G))
    (E : ℕ) (hLightDegree : ∀ v ∈ boundedLightLowVertices q T G, (lowNeighbors q G v).card ≤ E)
    (hNonlightDegree : ∀ v, signedDeficiency q G v = 0 → (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ E) :
    (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ E := by
  rcases hType with ⟨hRegular, hNotJ⟩ | hLight
  · have hNonhigh : 0 ≤ signedDeficiency q G y := by omega
    obtain ⟨_, hNot, _⟩ := positivePartner_nonhigh q G l y hLow hNonhigh hY
    have hNotS : l ∉ G.neighborFinset y ∩ boundedNonlightLowVertices q T G := by
      intro h
      exact hNot ((G.mem_neighborFinset y l).mp (Finset.mem_inter.mp h).1).symm
    have hSupport (w) (hNe : w ≠ y) (hNegative : weightedResidual q G w y < 0) :
        w ∈ G.neighborFinset y ∩ boundedNonlightLowVertices q T G ∨ w ∈ boundedLightTriangleRegularVertices q T G :=
      Or.inl (bounded_regular_negative_entry_support q T G hFree y w hRegular hNotJ hNe hNegative)
    exact (bounded_negative_support_column_exceptions q T G hFree l y hLow hY hNonhigh X
      (G.neighborFinset y ∩ boundedNonlightLowVertices q T G) hX hNonhighX hNotS hSupport hAvoid).trans
      (hNonlightDegree y hRegular)
  · have hUnit := (Finset.mem_filter.mp hLight).2.1
    have hNonhigh : 0 ≤ signedDeficiency q G y := by omega
    obtain ⟨_, hNot, _⟩ := positivePartner_nonhigh q G l y hLow hNonhigh hY
    have hNotS : l ∉ lowNeighbors q G y := by
      intro h
      exact hNot ((G.mem_neighborFinset y l).mp (Finset.mem_filter.mp h).1).symm
    have hSupport (w) (hNe : w ≠ y) (hNegative : weightedResidual q G w y < 0) :
        w ∈ lowNeighbors q G y ∨ w ∈ boundedLightTriangleRegularVertices q T G :=
      bounded_light_negative_entry_support q T G hFree y w hLight hNe hNegative
    exact (bounded_negative_support_column_exceptions q T G hFree l y hLow hY hNonhigh X
      (lowNeighbors q G y) hX hNonhighX hNotS hSupport hAvoid).trans (hLightDegree y hLight)

def boundedGoodPositivePartners {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  ((positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ boundedLightLowVertices q T G) \
    boundedLightTriangleRegularVertices q T G

theorem bounded_good_positivePartners_card_le (q C T B E F : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (X : Finset (Fin (q ^ 2 + q + 2))) (hX : X ⊆ G.neighborFinset l)
    (hNonhighX : ∀ x ∈ X, 0 ≤ signedDeficiency q G x)
    (hAvoid : ∀ x ∈ X, Disjoint (G.neighborFinset x) (boundedLightTriangleRegularVertices q T G))
    (hRows : ∀ x ∈ X, (positivePartners q G x).card ≤ B)
    (hLightDegree : ∀ v ∈ boundedLightLowVertices q T G, (lowNeighbors q G v).card ≤ E)
    (hNonlightDegree : ∀ v, signedDeficiency q G v = 0 → (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ E)
    (hMissing : (G.neighborFinset l \ X).card ≤ F) (hMany : 2 * E + 1 < X.card)
    (hOrder : 8 * C * (F + 2 * E + 1) < q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    (((positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ boundedLightLowVertices q T G).card : ℕ) ≤
      2 * B * (4 * B + 1) + (boundedLightTriangleRegularVertices q T G).card := by
  let Y := boundedGoodPositivePartners q T G l
  have hSpec (y) (hy : y ∈ Y) : y ∈ positivePartners q G l ∧
      ((signedDeficiency q G y = 0 ∧ y ∉ boundedLightTriangleRegularVertices q T G) ∨ y ∈ boundedLightLowVertices q T G) := by
    obtain ⟨hyFilter, hyNot⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hyP, hyType⟩ := Finset.mem_filter.mp hyFilter
    refine ⟨hyP, ?_⟩
    rcases hyType with hRegular | hLight
    · exact Or.inl ⟨hRegular, hyNot⟩
    · exact Or.inr hLight
  have hNonhighY (y) (hy : y ∈ Y) : 0 ≤ signedDeficiency q G y := by
    rcases (hSpec y hy).2 with ⟨hRegular, _⟩ | hLight
    · omega
    · have hUnit := (Finset.mem_filter.mp hLight).2.1
      omega
  have hExceptions (y) (hy : y ∈ Y) :
      (X.filter fun x => (weightedAdjacency q G * weightedResidual q G) x y < 1).card ≤ E :=
    bounded_regular_or_light_column_exceptions q T G hFree l y hLow (hSpec y hy).1 (hSpec y hy).2
      X hX hNonhighX hAvoid E hLightDegree hNonlightDegree
  have hBound := positive_row_propagation_bound q C B E F G hFree l X Y hX hLow hNonhighX hNonhighY
    hRows hExceptions hMissing hMany hOrder hNoCheap
  have hCard := Finset.card_le_card_sdiff_add_card
    (s := (positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ boundedLightLowVertices q T G)
    (t := boundedLightTriangleRegularVertices q T G)
  change _ ≤ Y.card + _ at hCard
  omega

/-- Bounded-branch propagation uses regular and light neighbors that avoid the exceptional regular set. -/
def boundedPropagationNeighbors {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n) : Finset (Fin n) :=
  ((G.neighborFinset l).filter fun x => signedDeficiency q G x = 0 ∨ x ∈ boundedLightLowVertices q T G).filter fun x =>
    Disjoint (G.neighborFinset x) (boundedLightTriangleRegularVertices q T G)

theorem boundedPropagationNeighbors_mem {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (l x : Fin n) :
    x ∈ boundedPropagationNeighbors q T G l ↔ x ∈ G.neighborFinset l ∧
      (signedDeficiency q G x = 0 ∨ x ∈ boundedLightLowVertices q T G) ∧
      Disjoint (G.neighborFinset x) (boundedLightTriangleRegularVertices q T G) := by
  simp only [boundedPropagationNeighbors, Finset.mem_filter, and_assoc]

theorem boundedPropagationNeighbors_missing_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (M : ℕ) (hNonlight : (G.neighborFinset l ∩ boundedNonlightLowVertices q T G).card ≤ M) :
    (G.neighborFinset l \ boundedPropagationNeighbors q T G l).card ≤ M + (highVertices q G).card +
      (boundedLightTriangleRegularVertices q T G).card := by
  let N := G.neighborFinset l
  let badType := N.filter fun x => ¬(signedDeficiency q G x = 0 ∨ x ∈ boundedLightLowVertices q T G)
  let hitJ := N.filter fun x => ∃ w ∈ boundedLightTriangleRegularVertices q T G, G.Adj x w
  have hBadCover : badType ⊆ (N ∩ boundedNonlightLowVertices q T G) ∪ highVertices q G := by
    intro x hx
    obtain ⟨hxN, hxBad⟩ := Finset.mem_filter.mp hx
    have hxNotZero : signedDeficiency q G x ≠ 0 := fun h => hxBad (Or.inl h)
    have hxNotLight : x ∉ boundedLightLowVertices q T G := fun h => hxBad (Or.inr h)
    by_cases hPositive : 0 < signedDeficiency q G x
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxN,
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPositive⟩, hxNotLight⟩⟩)
    · exact Finset.mem_union_right _ ((mem_highVertices_iff q G x).mpr (by omega))
  have hBadCard : badType.card ≤ M + (highVertices q G).card := by
    have h := (Finset.card_le_card hBadCover).trans (Finset.card_union_le _ _)
    change (N ∩ boundedNonlightLowVertices q T G).card ≤ M at hNonlight
    omega
  have hNotJ : l ∉ boundedLightTriangleRegularVertices q T G := by
    intro h
    have hZero := boundedLightTriangleRegularVertices_regular q T G l h
    omega
  have hJCard : hitJ.card ≤ (boundedLightTriangleRegularVertices q T G).card :=
    neighbor_hits_set_card_le G hFree l N _ (fun _ h => h) hNotJ
  have hCover : N \ boundedPropagationNeighbors q T G l ⊆ badType ∪ hitJ := by
    intro x hx
    obtain ⟨hxN, hxNot⟩ := Finset.mem_sdiff.mp hx
    by_cases hType : signedDeficiency q G x = 0 ∨ x ∈ boundedLightLowVertices q T G
    · by_cases hJ : Disjoint (G.neighborFinset x) (boundedLightTriangleRegularVertices q T G)
      · exact False.elim (hxNot ((boundedPropagationNeighbors_mem q T G l x).mpr ⟨hxN, hType, hJ⟩))
      · obtain ⟨w, hwN, hwJ⟩ := Finset.not_disjoint_iff.mp hJ
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hxN, w, hwJ, (G.mem_neighborFinset x w).mp hwN⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxN, hType⟩)
  have hTotal := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  change (N \ boundedPropagationNeighbors q T G l).card ≤ _
  omega

theorem boundedPropagationNeighbors_positive_card_le (q T K M : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hBound : ∀ w, signedDeficiency q G w ≤ K)
    (hIndependent : ∀ v ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj v w)
    (hTriangles : ∀ w ∈ boundedLightLowVertices q T G, (triangularRegularNeighbors q G w).card ≤ 16)
    (hNonlight : ∀ w, (G.neighborFinset w ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (l x : Fin (q ^ 2 + q + 2)) (hx : x ∈ boundedPropagationNeighbors q T G l) :
    (positivePartners q G x).card ≤ 17 + (boundedLightTriangleRegularVertices q T G).card +
      (highVertices q G).card + (K + 1) * M := by
  obtain ⟨_, hType, _⟩ := (boundedPropagationNeighbors_mem q T G l x).mp hx
  rcases hType with hRegular | hLight
  · have hRow := bounded_regular_positivePartners_card_bound q T G hFree hIndependent K (Nat.cast_nonneg K)
      hBound x hRegular M (by exact_mod_cast hNonlight x)
    have hRowNat : (positivePartners q G x).card ≤ 1 + (boundedLightTriangleRegularVertices q T G).card +
        (highVertices q G).card + (K + 1) * M := by exact_mod_cast hRow
    omega
  · have hRow := bounded_light_positivePartners_card_le q T G hFree K M (Nat.cast_nonneg K)
      hBound hIndependent x hLight (hTriangles x hLight) (by exact_mod_cast hNonlight x)
    have hRowNat : (positivePartners q G x).card ≤ 17 + (K + 1) * M + (highVertices q G).card := by
      exact_mod_cast hRow
    omega

/-- Every low vertex has boundedly many regular or light positive partners. -/
theorem bounded_low_positive_regular_light_bound (q C T K M : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hBound : ∀ w, signedDeficiency q G w ≤ K)
    (hIndependent : ∀ v ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj v w)
    (hTriangles : ∀ w ∈ boundedLightLowVertices q T G, (triangularRegularNeighbors q G w).card ≤ 16)
    (hNonlight : ∀ w, (G.neighborFinset w ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (l : Fin (q ^ 2 + q + 2)) (hLow : 1 ≤ signedDeficiency q G l)
    (hCount : K + (M + (highVertices q G).card + (boundedLightTriangleRegularVertices q T G).card) + 2 * M + 1 ≤ q)
    (hOrder : 8 * C * (M + (highVertices q G).card + (boundedLightTriangleRegularVertices q T G).card + 2 * M + 1) < q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y → q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4)) :
    let B := 17 + (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M
    ((positivePartners q G l).filter fun y => signedDeficiency q G y = 0 ∨ y ∈ boundedLightLowVertices q T G).card ≤
      2 * B * (4 * B + 1) + (boundedLightTriangleRegularVertices q T G).card := by
  let X := boundedPropagationNeighbors q T G l
  let F := M + (highVertices q G).card + (boundedLightTriangleRegularVertices q T G).card
  let B := 17 + (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M
  have hX : X ⊆ G.neighborFinset l := fun x hx => ((boundedPropagationNeighbors_mem q T G l x).mp hx).1
  have hNonhighX (x) (hx : x ∈ X) : 0 ≤ signedDeficiency q G x := by
    rcases ((boundedPropagationNeighbors_mem q T G l x).mp hx).2.1 with hRegular | hLight
    · omega
    · have hUnit := (Finset.mem_filter.mp hLight).2.1
      omega
  have hAvoid (x) (hx : x ∈ X) : Disjoint (G.neighborFinset x) (boundedLightTriangleRegularVertices q T G) :=
    ((boundedPropagationNeighbors_mem q T G l x).mp hx).2.2
  have hRows (x) (hx : x ∈ X) : (positivePartners q G x).card ≤ B :=
    boundedPropagationNeighbors_positive_card_le q T K M G hFree hBound hIndependent hTriangles hNonlight l x hx
  have hLightDegree (w) (hw : w ∈ boundedLightLowVertices q T G) : (lowNeighbors q G w).card ≤ M := by
    rw [bounded_light_lowNeighbors_eq_nonlight q T G hIndependent w hw]
    exact hNonlight w
  have hMissing : (G.neighborFinset l \ X).card ≤ F :=
    boundedPropagationNeighbors_missing_card_le q T G hFree l hLow M (hNonlight l)
  have hDegree : q + 1 ≤ G.degree l + K := by
    have h := hBound l
    unfold signedDeficiency at h
    omega
  have hPartition := Finset.card_sdiff_add_card_eq_card hX
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hPartition
  have hMany : 2 * M + 1 < X.card := by
    change K + F + 2 * M + 1 ≤ q at hCount
    omega
  exact bounded_good_positivePartners_card_le q C T B M F G hFree l hLow X hX hNonhighX hAvoid hRows
    hLightDegree (fun w _ => hNonlight w) hMissing hMany hOrder hNoCheap

theorem bounded_active_neighbors_of_upper_scale (q C K T D₀ : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKq : K ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hHigh : (highVertices q G).card ≤ q)
    (hNoCheap : ∀ x y (hxy : x ≠ y), ¬G.Adj x y →
      q ≤ C * (withEdge G x y hxy).copyCount (cycleGraph 4))
    (hBound : ∀ v, signedDeficiency q G v ≤ K)
    (hScale : 400 * (8 * C) * (K + (highVertices q G).card + 3) ^ 3 ≤ D₀)
    (hT : 16 * D₀ * (K + 1) ≤ T) (hq : 16 * D₀ ≤ q)
    (hSize : 16 * (K + 4) ^ 2 * (16 * D₀) ^ 3 ≤ q)
    (hOverlapT : 24 * (2 * D₀) ^ 2 * K ≤ T)
    (hOverlapQ : 12 * (2 * D₀) ^ 2 * (2 + K ^ 2) ≤ q) (x : Fin (q ^ 2 + q + 2)) :
    (G.neighborFinset x ∩ boundedActiveLowVertices q T G).card ≤ 18 * (2 * D₀) ^ 2 := by
  let D := 400 * (8 * C) * (K + (highVertices q G).card + 3) ^ 3
  have hDD : D ≤ D₀ := hScale
  have hEq : (D : ℤ) = 400 * (8 * (C : ℤ)) * ((K : ℤ) + (highVertices q G).card + 3) ^ 3 := by
    simp [D]
  have hTActual : 16 * D * (K + 1) ≤ T := by
    calc
      _ ≤ 16 * D₀ * (K + 1) := by gcongr
      _ ≤ _ := hT
  have hqActual : 16 * D ≤ q := (Nat.mul_le_mul_left 16 hDD).trans hq
  have hSizeActual : 16 * (K + 4) ^ 2 * (16 * D) ^ 3 ≤ q := by
    calc
      _ ≤ 16 * (K + 4) ^ 2 * (16 * D₀) ^ 3 := by gcongr
      _ ≤ _ := hSize
  have hOverlapTActual : 24 * (2 * D) ^ 2 * K ≤ T := by
    calc
      _ ≤ 24 * (2 * D₀) ^ 2 * K := by gcongr
      _ ≤ _ := hOverlapT
  have hOverlapQActual : 12 * (2 * D) ^ 2 * (2 + K ^ 2) ≤ q := by
    calc
      _ ≤ 12 * (2 * D₀) ^ 2 * (2 + K ^ 2) := by gcongr
      _ ≤ _ := hOverlapQ
  have hCount := boundedActiveLowVertices_neighbor_card_le q C K T hC hK hKq G hFree hDegree hDense hHigh
    hNoCheap hBound D hEq (by exact_mod_cast hTActual) (by exact_mod_cast hqActual)
    (by exact_mod_cast hSizeActual) (by exact_mod_cast hOverlapTActual) (by exact_mod_cast hOverlapQActual) x
  have hCountNat : (G.neighborFinset x ∩ boundedActiveLowVertices q T G).card ≤ 18 * (2 * D) ^ 2 := by
    exact_mod_cast hCount
  exact hCountNat.trans (by gcongr)

/-- The claimed bound supplies all bounded-branch light and positive-row estimates with fixed constants. -/
theorem claimedBound_uniform_light_structure (hBound : ClaimedBound) :
    ∃ C K T M B Q : ℕ, 1 ≤ C ∧ 1 ≤ K ∧ ∃ N : ℕ, ∀ r : ℕ, N ≤ 2 ^ r →
      ∀ G : SimpleGraph (Fin ((2 ^ r) ^ 2 + 2 ^ r + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ r) ^ 2 + 2 ^ r + 2) (cycleGraph 4) →
        (∀ v, signedDeficiency (2 ^ r) G v ≤ K) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ r) T G, ∀ w ∈ boundedLightLowVertices (2 ^ r) T G, ¬G.Adj l w) ∧
        (∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices (2 ^ r) T G).card ≤ M) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ r) T G,
          (triangularRegularNeighbors (2 ^ r) G l).card ≤ 16 ∧ (positivePartners (2 ^ r) G l).card ≤ B) ∧
        (boundedLightTriangleRegularVertices (2 ^ r) T G).card ≤ 72 ∧
        (∀ v, signedDeficiency (2 ^ r) G v = 0 → (positivePartners (2 ^ r) G v).card ≤ B) ∧
        (∀ v, 1 ≤ signedDeficiency (2 ^ r) G v →
          ((positivePartners (2 ^ r) G v).filter fun y => signedDeficiency (2 ^ r) G y = 0 ∨
            y ∈ boundedLightLowVertices (2 ^ r) T G).card ≤ Q) := by
  obtain ⟨C, hC, N₀, hPrep⟩ := claimedBound_uniform_preparation hBound
  obtain ⟨K, hK, N₁, hGlobal⟩ := claimedBound_uniform_bounded_deficiency hBound
  let H := 2611456 * C
  let D := 400 * (8 * C) * (K + H + 3) ^ 3
  let T := 1 + 16 * D * (K + 1) + 24 * (2 * D) ^ 2 * K + 8 * (K + 1)
  let M := 18 * T ^ 2 + 18 * (2 * D) ^ 2
  let B := 17 + 72 + H + (K + 1) * M
  let F := M + H + 72
  let Q := 2 * B * (4 * B + 1) + 72
  let cutoff := N₀ + N₁ + K + H + 48 * C + 24 + 16 * D +
    16 * (K + 4) ^ 2 * (16 * D) ^ 3 + 12 * (2 * D) ^ 2 * (2 + K ^ 2) +
    6 * T ^ 2 + 4 * (2 * H + 33) + 2 * (M + H + K * M + 17) +
    (K + F + 2 * M + 1) + (8 * C * (F + 2 * M + 1) + 1)
  refine ⟨C, K, T, M, B, Q, hC, hK, cutoff, ?_⟩
  intro r hr G hFree hEdges
  let q := 2 ^ r
  have hCutoff : cutoff ≤ q := hr
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₁ : N₁ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hKq : K ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHq : H ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have h48 : 48 * C ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have h24 : 24 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have h16D : 16 * D ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hSize : 16 * (K + 4) ^ 2 * (16 * D) ^ 3 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hOverlapQ : 12 * (2 * D) ^ 2 * (2 + K ^ 2) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHubOrder : 6 * T ^ 2 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hLightOrder : 4 * (2 * H + 33) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hJOrder : 2 * (M + H + K * M + 17) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hPropCount : K + F + 2 * M + 1 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hPropOrder : 8 * C * (F + 2 * M + 1) < q := by dsimp only [cutoff] at hCutoff; omega
  have hT : 1 ≤ T := by dsimp only [T]; omega
  have hTScale : 16 * D * (K + 1) ≤ T := by dsimp only [T]; omega
  have hTOverlap : 24 * (2 * D) ^ 2 * K ≤ T := by dsimp only [T]; omega
  have hTLight : 8 * (K + 1) ≤ T := by dsimp only [T]; omega
  have hT8 : 8 ≤ T := by omega
  obtain ⟨hExcess, hGraphs⟩ := hPrep r hN₀
  obtain ⟨hNoCheap, _hMin, hDegree, hHigh, _hPositive⟩ := hGraphs G hFree hEdges
  change q ≤ 4 * C * abovePlaneExcess q ^ 2 at hExcess
  change (∀ v, G.degree v ≤ q + 2) at hDegree
  change (highVertices q G).card ≤ H at hHigh
  have hBoundG : ∀ v, signedDeficiency q G v ≤ K := hGlobal r hN₁ G hFree hEdges
  have hHighQ := hHigh.trans hHq
  have hExcessThree : 3 ≤ abovePlaneExcess q := by
    by_contra h
    have hSmall : abovePlaneExcess q ≤ 2 := by omega
    have hSquare : abovePlaneExcess q ^ 2 ≤ 4 := by nlinarith only [hSmall]
    have hProduct := Nat.mul_le_mul_left (4 * C) hSquare
    omega
  have hDense := extremal_density_of_excess q G hEdges hExcessThree
  have hLowSize := dense_lowVertices_card_le q G hDegree hDense hHighQ
  have hPositiveTotal := dense_positiveDeficiency_le_high_card q G hDegree hDense
  have hHighInt : ((highVertices q G).card : ℤ) ≤ q := by exact_mod_cast hHighQ
  have hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ) := hPositiveTotal.trans (by omega)
  have hScale : 400 * (8 * C) * (K + (highVertices q G).card + 3) ^ 3 ≤ D := by
    dsimp only [D]
    gcongr
  have hActive (v) : (G.neighborFinset v ∩ boundedActiveLowVertices q T G).card ≤ 18 * (2 * D) ^ 2 :=
    bounded_active_neighbors_of_upper_scale q C K T D hC hK hKq G hFree hDegree hDense hHighQ
      hNoCheap hBoundG hScale hTScale h16D hSize hTOverlap hOverlapQ v
  have hHubs : (lowHubs q T G).card ≤ 18 * T ^ 2 := by
    exact_mod_cast lowHubs_card_le q T hT hHubOrder G hFree hLowSize
  have hNonlight (v) : (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M := by
    have h := bounded_nonlight_neighbor_card_le q T G v (18 * (2 * D) ^ 2)
      (by exact_mod_cast hActive v)
    have hn : (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤
        (lowHubs q T G).card + 18 * (2 * D) ^ 2 := by exact_mod_cast h
    dsimp only [M]
    omega
  have hLightOrderActual : 4 * (2 * ((highVertices q G).card : ℤ) + 33) ≤ q := by
    have hh : ((highVertices q G).card : ℤ) ≤ H := by exact_mod_cast hHigh
    have ho : 4 * (2 * (H : ℤ) + 33) ≤ q := by exact_mod_cast hLightOrder
    omega
  have hIndependent := boundedLightLowVertices_independent q T (by omega) K (Nat.cast_nonneg K)
    G hFree hBoundG (by exact_mod_cast hTLight) hTotal hLightOrderActual
  have hTriangles (l) (hl : l ∈ boundedLightLowVertices q T G) :
      (triangularRegularNeighbors q G l).card ≤ 16 := by
    obtain ⟨hlOut, hlUnit, hlLight⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlLow, hlNotHub⟩ := Finset.mem_sdiff.mp hlOut
    have hFew := (bounded_outside_lowHubs_bounds q T K G hBoundG l hlLow hlNotHub).2.2
    have hScaled := mul_le_mul_of_nonneg_right (show (8 : ℤ) ≤ T by exact_mod_cast hT8)
      (Nat.cast_nonneg (α := ℤ) (lowNeighbors q G l).card)
    exact light_unit_triangle_bound q (by omega) G hFree l hlUnit (by omega) (by omega) hTotal (by omega)
  have hLightDegree (l) (hl : l ∈ boundedLightLowVertices q T G) : ((lowNeighbors q G l).card : ℤ) ≤ M := by
    rw [bounded_light_lowNeighbors_eq_nonlight q T G hIndependent l hl]
    exact_mod_cast hNonlight l
  have hJOrderActual : 2 * ((M : ℤ) + (highVertices q G).card + K * M + 17) ≤ q := by
    have hh : ((highVertices q G).card : ℤ) ≤ H := by exact_mod_cast hHigh
    have ho : 2 * ((M : ℤ) + H + K * M + 17) ≤ q := by exact_mod_cast hJOrder
    omega
  have hJ : (boundedLightTriangleRegularVertices q T G).card ≤ 72 := by
    exact_mod_cast boundedLightTriangleRegularVertices_card_le q T G hFree K M M (Nat.cast_nonneg K)
      hBoundG hLightDegree hTriangles (fun v => by exact_mod_cast hNonlight v) hLowSize hJOrderActual h24
  refine ⟨hBoundG, hIndependent, hNonlight, ?_, hJ, ?_, ?_⟩
  · intro l hl
    refine ⟨hTriangles l hl, ?_⟩
    have hRow := bounded_light_positivePartners_card_le q T G hFree K M (Nat.cast_nonneg K)
      hBoundG hIndependent l hl (hTriangles l hl) (by exact_mod_cast hNonlight l)
    have hRowNat : (positivePartners q G l).card ≤ 17 + (K + 1) * M + (highVertices q G).card := by
      exact_mod_cast hRow
    change (positivePartners q G l).card ≤ 17 + 72 + H + (K + 1) * M
    exact hRowNat.trans (by omega)
  · intro v hv
    have hRow := bounded_regular_positivePartners_card_bound q T G hFree hIndependent K (Nat.cast_nonneg K)
      hBoundG v hv M (by exact_mod_cast hNonlight v)
    have hRowNat : (positivePartners q G v).card ≤ 1 + (boundedLightTriangleRegularVertices q T G).card +
        (highVertices q G).card + (K + 1) * M := by exact_mod_cast hRow
    change (positivePartners q G v).card ≤ 17 + 72 + H + (K + 1) * M
    exact hRowNat.trans (by omega)
  · intro v hv
    have hCountActual : K + (M + (highVertices q G).card + (boundedLightTriangleRegularVertices q T G).card) +
        2 * M + 1 ≤ q := by dsimp only [F] at hPropCount; omega
    have hF : M + (highVertices q G).card + (boundedLightTriangleRegularVertices q T G).card ≤ F := by
      dsimp only [F]; omega
    have hScaled := Nat.mul_le_mul_left (8 * C) (Nat.add_le_add_right hF (2 * M + 1))
    have hOrderActual : 8 * C * (M + (highVertices q G).card +
        (boundedLightTriangleRegularVertices q T G).card + 2 * M + 1) < q := by
      apply lt_of_le_of_lt _ hPropOrder
      simpa only [Nat.add_assoc] using hScaled
    have hRow := bounded_low_positive_regular_light_bound q C T K M G hFree hBoundG hIndependent
      hTriangles hNonlight v hv hCountActual hOrderActual hNoCheap
    let B₀ := 17 + (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + (K + 1) * M
    have hB₀ : B₀ ≤ B := by dsimp only [B₀, B]; omega
    change _ ≤ 2 * B₀ * (4 * B₀ + 1) + (boundedLightTriangleRegularVertices q T G).card at hRow
    apply hRow.trans
    dsimp only [Q]
    gcongr

/-- Light neighbors that extend across an untriangulated edge to the other neighborhood. -/
def boundedLightPathVertices {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (v w : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v ∩ boundedLightLowVertices q T G).filter fun x =>
    ∃ y ∈ G.neighborFinset w, G.Adj x y ∧ codegree G x y = 0

/-- All but a bounded number of light neighbors extend to a path contributing to the defect-matrix identity. -/
theorem bounded_light_path_vertices_lower (q T M Q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ x ∈ boundedLightLowVertices q T G, ¬G.Adj l x)
    (hNonlight : ∀ x, (G.neighborFinset x ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (v w : Fin (q ^ 2 + q + 2)) (hNe : v ≠ w)
    (hPartners : (positivePartners q G w ∩ boundedLightLowVertices q T G).card ≤ Q) :
    (G.neighborFinset v ∩ boundedLightLowVertices q T G).card ≤
      (boundedLightPathVertices q T G v w).card + Q + 2 +
        2 * ((boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + M) := by
  let L := boundedLightLowVertices q T G
  let X := G.neighborFinset v ∩ L
  let P := boundedLightPathVertices q T G v w
  let A := insert w ((G.neighborFinset v ∩ G.neighborFinset w) ∪ (positivePartners q G w ∩ L))
  let Y := boundedLightTriangleRegularVertices q T G ∪ highVertices q G ∪
    (G.neighborFinset w ∩ boundedNonlightLowVertices q T G)
  let H := (G.neighborFinset v).filter fun x => ∃ y ∈ Y.erase v, G.Adj x y
  let C := boundedTriangularLightNeighbors q T G v
  have hY : Y.card ≤ (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + M := by
    have h₁ := Finset.card_union_le (boundedLightTriangleRegularVertices q T G) (highVertices q G)
    have h₂ := Finset.card_union_le (boundedLightTriangleRegularVertices q T G ∪ highVertices q G)
      (G.neighborFinset w ∩ boundedNonlightLowVertices q T G)
    dsimp only [Y]
    have hw := hNonlight w
    omega
  have hH : H.card ≤ Y.card := by
    have hNot : v ∉ Y.erase v := by simp
    have h := neighbor_hits_set_card_le G hFree v (G.neighborFinset v) (Y.erase v) (fun _ hx => hx) hNot
    exact h.trans Finset.card_erase_le
  have hC : C.card ≤ (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + M := by
    have h := bounded_triangular_light_neighbor_card_le q T G hFree hIndependent v
    have hv := hNonlight v
    dsimp only [C]
    omega
  have hA : A.card ≤ Q + 2 := by
    have hInsert := Finset.card_insert_le w ((G.neighborFinset v ∩ G.neighborFinset w) ∪
      (positivePartners q G w ∩ L))
    have hUnion := Finset.card_union_le (G.neighborFinset v ∩ G.neighborFinset w) (positivePartners q G w ∩ L)
    have hCodegree := codegree_le_one G hFree v w hNe
    change (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1 at hCodegree
    dsimp only [A]
    change (positivePartners q G w ∩ L).card ≤ Q at hPartners
    omega
  have hCover : X \ P ⊆ A ∪ H ∪ C := by
    intro x hx
    obtain ⟨hxX, hxNotPath⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxN, hxL⟩ := Finset.mem_inter.mp hxX
    have hVX := (G.mem_neighborFinset v x).mp hxN
    by_cases hxA : x ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxA)
    have hXW : x ≠ w := by
      intro h
      apply hxA
      dsimp only [A]
      rw [h]
      exact Finset.mem_insert_self _ _
    have hNotAdj : ¬G.Adj w x := by
      intro h
      apply hxA
      dsimp only [A]
      apply Finset.mem_insert_of_mem
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxN, (G.mem_neighborFinset w x).mpr h⟩)
    have hNotPartner : x ∉ positivePartners q G w := by
      intro h
      apply hxA
      dsimp only [A]
      apply Finset.mem_insert_of_mem
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, hxL⟩)
    have hCodegree : codegree G x w = 1 := by
      have hUpper := codegree_le_one G hFree x w hXW
      by_contra h
      have hZero : codegree G x w = 0 := by omega
      have hZeroRev : codegree G w x = 0 := by rw [codegree_symm]; exact hZero
      have hEntry := weightedResidual_nonadj q G w x hXW.symm hNotAdj
      rw [hZeroRev] at hEntry
      apply hNotPartner
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < codegree G x w by omega)
    obtain ⟨hyX, hyW⟩ := Finset.mem_inter.mp hy
    have hXY := (G.mem_neighborFinset x y).mp hyX
    have hWY := (G.mem_neighborFinset w y).mp hyW
    have hyNotLight : y ∉ L := fun hyL => hIndependent x hxL y hyL hXY
    have hXYCodegree : codegree G x y = 1 := by
      have hUpper := codegree_le_one G hFree x y hXY.ne
      by_contra h
      have hZero : codegree G x y = 0 := by omega
      apply hxNotPath
      exact Finset.mem_filter.mpr ⟨hxX, y, hyW, hXY, hZero⟩
    by_cases hyV : y = v
    · apply Finset.mem_union_right
      change x ∈ boundedTriangularLightNeighbors q T G v
      apply Finset.mem_filter.mpr
      refine ⟨hxN, hxL, ?_⟩
      rw [codegree_symm, ← hyV]
      exact hXYCodegree
    · have hyY : y ∈ Y := by
        by_cases hRegular : signedDeficiency q G y = 0
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          apply Finset.mem_biUnion.mpr
          refine ⟨x, hxL, ?_⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyX, hRegular⟩, hXYCodegree⟩
        · by_cases hLow : 0 < signedDeficiency q G y
          · apply Finset.mem_union_right
            exact Finset.mem_inter.mpr ⟨hyW, Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLow⟩, hyNotLight⟩⟩
          · apply Finset.mem_union_left
            apply Finset.mem_union_right
            exact (mem_highVertices_iff q G y).mpr (by omega)
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hxN, y, Finset.mem_erase.mpr ⟨hyV, hyY⟩, hXY⟩
  have hBad := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hFirst := Finset.card_union_le A H
  have hSubset : P ⊆ X := Finset.filter_subset _ _
  have hPartition := Finset.card_sdiff_add_card_eq_card hSubset
  change X.card ≤ P.card + Q + 2 + 2 * ((boundedLightTriangleRegularVertices q T G).card +
    (highVertices q G).card + M)
  omega

/-- Two opposite cross-parts of a nonnegative matrix fit inside the whole rectangular sum. -/
theorem cross_partition_sum_le {ι : Type*} [DecidableEq ι]
    (S T L : Finset ι) (f : ι → ι → ℤ) (hNonneg : ∀ x y, 0 ≤ f x y) :
    (∑ x ∈ S ∩ L, ∑ y ∈ T \ L, f x y) + (∑ x ∈ S \ L, ∑ y ∈ T ∩ L, f x y) ≤
      ∑ x ∈ S, ∑ y ∈ T, f x y := by
  have hLeft : (∑ x ∈ S ∩ L, ∑ y ∈ T \ L, f x y) ≤ ∑ x ∈ S ∩ L, ∑ y ∈ T, f x y := by
    apply Finset.sum_le_sum
    intro x _
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun y _ _ => hNonneg x y)
  have hRight : (∑ x ∈ S \ L, ∑ y ∈ T ∩ L, f x y) ≤ ∑ x ∈ S \ L, ∑ y ∈ T, f x y := by
    apply Finset.sum_le_sum
    intro x _
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun y _ _ => hNonneg x y)
  have hPart := Finset.sum_sdiff (f := fun x => ∑ y ∈ T, f x y) (Finset.inter_subset_left (s₁ := S) (s₂ := L))
  have hSet : S \ (S ∩ L) = S \ L := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hSet] at hPart
  omega

/-- Every retained light neighbor contributes at least one to a cross-part of the zero-codegree walk matrix. -/
theorem bounded_light_path_walk_lower (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ x ∈ boundedLightLowVertices q T G, ¬G.Adj l x)
    (v w : Fin (q ^ 2 + q + 2)) :
    ((boundedLightPathVertices q T G v w).card : ℤ) ≤
      ∑ x ∈ G.neighborFinset v ∩ boundedLightLowVertices q T G,
        ∑ y ∈ G.neighborFinset w \ boundedLightLowVertices q T G, (zeroCodegreeGraph G).adjMatrix ℤ x y := by
  let P := boundedLightPathVertices q T G v w
  let f := fun x => ∑ y ∈ G.neighborFinset w \ boundedLightLowVertices q T G,
    (zeroCodegreeGraph G).adjMatrix ℤ x y
  have hNonneg (x y) : (0 : ℤ) ≤ (zeroCodegreeGraph G).adjMatrix ℤ x y := by
    simp only [SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have hEach (x) (hx : x ∈ P) : (1 : ℤ) ≤ f x := by
    obtain ⟨hxSet, y, hyW, hXY, hZero⟩ := Finset.mem_filter.mp hx
    have hxLight := (Finset.mem_inter.mp hxSet).2
    have hyNot : y ∉ boundedLightLowVertices q T G := fun hy => hIndependent x hxLight y hy hXY
    have hySet : y ∈ G.neighborFinset w \ boundedLightLowVertices q T G := Finset.mem_sdiff.mpr ⟨hyW, hyNot⟩
    have hAdj : (zeroCodegreeGraph G).Adj x y := ⟨hXY.ne, hZero⟩
    have hTerm := Finset.single_le_sum (fun z (_ : z ∈ G.neighborFinset w \ boundedLightLowVertices q T G) =>
      hNonneg x z) hySet
    change (zeroCodegreeGraph G).adjMatrix ℤ x y ≤ f x at hTerm
    simpa only [SimpleGraph.adjMatrix_apply, ite_eq_left hAdj] using hTerm
  have hSubset : P ⊆ G.neighborFinset v ∩ boundedLightLowVertices q T G := Finset.filter_subset _ _
  calc
    _ = ∑ _x ∈ P, (1 : ℤ) := by simp [P]
    _ ≤ ∑ x ∈ P, f x := Finset.sum_le_sum hEach
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun x _ _ =>
      Finset.sum_nonneg (fun y _ => hNonneg x y))

/-- The two orientations of the light paths occupy disjoint cross-parts of the walk matrix. -/
theorem bounded_light_paths_sum_le_walk (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ x ∈ boundedLightLowVertices q T G, ¬G.Adj l x)
    (v w : Fin (q ^ 2 + q + 2)) :
    ((boundedLightPathVertices q T G v w).card : ℤ) + (boundedLightPathVertices q T G w v).card ≤
      (G.adjMatrix ℤ * (zeroCodegreeGraph G).adjMatrix ℤ * G.adjMatrix ℤ) v w := by
  let L := boundedLightLowVertices q T G
  let f := fun x y => (zeroCodegreeGraph G).adjMatrix ℤ x y
  have hNonneg (x y) : 0 ≤ f x y := by
    dsimp only [f]
    simp only [SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have hSymm (x y) : f x y = f y x := by
    simp only [f, SimpleGraph.adjMatrix_apply, SimpleGraph.adj_comm]
  have hReverse : (∑ y ∈ G.neighborFinset w ∩ L, ∑ x ∈ G.neighborFinset v \ L, f y x) =
      ∑ x ∈ G.neighborFinset v \ L, ∑ y ∈ G.neighborFinset w ∩ L, f x y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hSymm y x
  have hLeft := bounded_light_path_walk_lower q T G hIndependent v w
  have hRight := bounded_light_path_walk_lower q T G hIndependent w v
  change _ ≤ ∑ y ∈ G.neighborFinset w ∩ L, ∑ x ∈ G.neighborFinset v \ L, f y x at hRight
  rw [hReverse] at hRight
  have hCross := cross_partition_sum_le (G.neighborFinset v) (G.neighborFinset w) L f hNonneg
  have hWalk : (G.adjMatrix ℤ * (zeroCodegreeGraph G).adjMatrix ℤ * G.adjMatrix ℤ) v w =
      ∑ x ∈ G.neighborFinset v, ∑ y ∈ G.neighborFinset w, f x y := by
    rw [Matrix.mul_assoc, G.adjMatrix_mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    exact G.mul_adjMatrix_apply _ x w
  rw [hWalk]
  change _ ≤ ∑ x ∈ G.neighborFinset v ∩ L, ∑ y ∈ G.neighborFinset w \ L, f x y at hLeft
  linarith only [hLeft, hRight, hCross]

/-- Light paths cancel the neighboring deficiency terms up to a fixed error. -/
theorem bounded_neighbor_weights_le_walk (q T K M Q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hBound : ∀ x, signedDeficiency q G x ≤ K)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ x ∈ boundedLightLowVertices q T G, ¬G.Adj l x)
    (hNonlight : ∀ x, (G.neighborFinset x ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (v w : Fin (q ^ 2 + q + 2)) (hNe : v ≠ w)
    (hVPartners : (positivePartners q G v ∩ boundedLightLowVertices q T G).card ≤ Q)
    (hWPartners : (positivePartners q G w ∩ boundedLightLowVertices q T G).card ≤ Q) :
    (∑ x ∈ G.neighborFinset v, positiveDeficiency q G x) +
        (∑ x ∈ G.neighborFinset w, positiveDeficiency q G x) ≤
      (G.adjMatrix ℤ * (zeroCodegreeGraph G).adjMatrix ℤ * G.adjMatrix ℤ) v w +
        2 * (Q + 2 + 2 * ((boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + M) : ℤ) +
        2 * K * M := by
  have hV := bounded_light_path_vertices_lower q T M Q G hFree hIndependent hNonlight v w hNe hWPartners
  have hW := bounded_light_path_vertices_lower q T M Q G hFree hIndependent hNonlight w v hNe.symm hVPartners
  have hVInt : ((G.neighborFinset v ∩ boundedLightLowVertices q T G).card : ℤ) ≤
      (boundedLightPathVertices q T G v w).card + Q + 2 +
        2 * ((boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + M) := by exact_mod_cast hV
  have hWInt : ((G.neighborFinset w ∩ boundedLightLowVertices q T G).card : ℤ) ≤
      (boundedLightPathVertices q T G w v).card + Q + 2 +
        2 * ((boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + M) := by exact_mod_cast hW
  have hWalk := bounded_light_paths_sum_le_walk q T G hIndependent v w
  have hWeightV := bounded_neighbor_positive_weight q T K (Nat.cast_nonneg K) G hBound v
  have hWeightW := bounded_neighbor_positive_weight q T K (Nat.cast_nonneg K) G hBound w
  have hScaleV := mul_le_mul_of_nonneg_left (show ((G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤ M
    by exact_mod_cast hNonlight v) (Nat.cast_nonneg (α := ℤ) K)
  have hScaleW := mul_le_mul_of_nonneg_left (show ((G.neighborFinset w ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤ M
    by exact_mod_cast hNonlight w) (Nat.cast_nonneg (α := ℤ) K)
  linarith only [hVInt, hWInt, hWalk, hWeightV, hWeightW, hScaleV, hScaleW]

/-- Positive-codegree low pairs have a uniformly bounded common zero-codegree neighborhood. -/
theorem bounded_common_zeroCodegree_partners_le (q T K M Q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2) (hBound : ∀ x, signedDeficiency q G x ≤ K)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ x ∈ boundedLightLowVertices q T G, ¬G.Adj l x)
    (hNonlight : ∀ x, (G.neighborFinset x ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (v w : Fin (q ^ 2 + q + 2)) (hNe : v ≠ w) (hCodegree : codegree G v w = 1)
    (_hV : 0 ≤ signedDeficiency q G v) (hW : 0 ≤ signedDeficiency q G w)
    (hVPartners : (positivePartners q G v ∩ boundedLightLowVertices q T G).card ≤ Q)
    (hWPartners : (positivePartners q G w ∩ boundedLightLowVertices q T G).card ≤ Q) :
    (codegree (zeroCodegreeGraph G) v w : ℤ) ≤ 6 + (K : ℤ) ^ 2 + 2 * Q +
      4 * ((boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + M) + 2 * K * M := by
  have hIdentity := defectMatrix_pair_identity q G hFree v w hNe hCodegree
  have hExpand : G.adjMatrix ℤ * defectMatrix q G * G.adjMatrix ℤ =
      G.adjMatrix ℤ * (zeroCodegreeGraph G).adjMatrix ℤ * G.adjMatrix ℤ +
      G.adjMatrix ℤ * Matrix.diagonal (signedDeficiency q G) * G.adjMatrix ℤ := by
    unfold defectMatrix
    noncomm_ring
  rw [defectMatrix_square_at_codegree_one q G v w hNe hCodegree,
    hExpand, Matrix.add_apply, adjMatrix_square_codegree, adjMatrix_diagonal_adjMatrix] at hIdentity
  have hLower := Finset.sum_le_sum (fun x (_ : x ∈ G.neighborFinset v ∩ G.neighborFinset w) =>
    signedDeficiency_ge_neg_one q G hDegree x)
  have hCard : ((G.neighborFinset v ∩ G.neighborFinset w).card : ℤ) = 1 := by exact_mod_cast hCodegree
  simp only [Finset.sum_const, nsmul_eq_mul, hCard] at hLower
  have hProduct := mul_le_mul (hBound v) (hBound w) hW (Nat.cast_nonneg (α := ℤ) K)
  have hVPositive : (∑ x ∈ G.neighborFinset v, signedDeficiency q G x) ≤
      ∑ x ∈ G.neighborFinset v, positiveDeficiency q G x :=
    Finset.sum_le_sum (fun _ _ => le_max_left _ _)
  have hWPositive : (∑ x ∈ G.neighborFinset w, signedDeficiency q G x) ≤
      ∑ x ∈ G.neighborFinset w, positiveDeficiency q G x :=
    Finset.sum_le_sum (fun _ _ => le_max_left _ _)
  have hWalk := bounded_neighbor_weights_le_walk q T K M Q G hFree hBound hIndependent hNonlight
    v w hNe hVPartners hWPartners
  nlinarith only [hIdentity, hLower, hProduct, hVPositive, hWPositive, hWalk]

/-- Under the claimed bound, positive-codegree low pairs have a fixed common zero-codegree bound. -/
theorem claimedBound_uniform_common_zeroCodegree (hBound : ClaimedBound) :
    ∃ E N : ℕ, ∀ r : ℕ, N ≤ 2 ^ r →
      ∀ G : SimpleGraph (Fin ((2 ^ r) ^ 2 + 2 ^ r + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ r) ^ 2 + 2 ^ r + 2) (cycleGraph 4) →
        ∀ v w, v ≠ w → codegree G v w = 1 → 1 ≤ signedDeficiency (2 ^ r) G v →
          1 ≤ signedDeficiency (2 ^ r) G w → codegree (zeroCodegreeGraph G) v w ≤ E := by
  obtain ⟨_C, K, T, M, _B, Q, _hC, _hK, N₀, hStructure⟩ := claimedBound_uniform_light_structure hBound
  obtain ⟨C₀, _hC₀, N₁, hPrep⟩ := claimedBound_uniform_preparation hBound
  let H := 2611456 * C₀
  let E := 6 + K ^ 2 + 2 * Q + 4 * (72 + H + M) + 2 * K * M
  refine ⟨E, N₀ + N₁, ?_⟩
  intro r hr G hFree hEdges v w hNe hCodegree hV hW
  have hN₀ : N₀ ≤ 2 ^ r := by omega
  have hN₁ : N₁ ≤ 2 ^ r := by omega
  obtain ⟨hGlobal, hIndependent, hNonlight, _hLights, hJ, _hRegular, hRows⟩ :=
    hStructure r hN₀ G hFree hEdges
  obtain ⟨_hExcess, hGraphs⟩ := hPrep r hN₁
  obtain ⟨_hNoCheap, _hMin, hDegree, hHigh, _hPositive⟩ := hGraphs G hFree hEdges
  have hPartners (x) (hx : 1 ≤ signedDeficiency (2 ^ r) G x) :
      (positivePartners (2 ^ r) G x ∩ boundedLightLowVertices (2 ^ r) T G).card ≤ Q := by
    apply (Finset.card_le_card ?_).trans (hRows x hx)
    intro y hy
    obtain ⟨hyP, hyLight⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_filter.mpr ⟨hyP, Or.inr hyLight⟩
  have hLocal := bounded_common_zeroCodegree_partners_le (2 ^ r) T K M Q G hFree hDegree hGlobal
    hIndependent hNonlight v w hNe hCodegree (by omega) (by omega) (hPartners v hV) (hPartners w hW)
  have hJInt : ((boundedLightTriangleRegularVertices (2 ^ r) T G).card : ℤ) ≤ 72 := by exact_mod_cast hJ
  have hHighInt : ((highVertices (2 ^ r) G).card : ℤ) ≤ H := by exact_mod_cast hHigh
  have hFinal : (codegree (zeroCodegreeGraph G) v w : ℤ) ≤
      6 + (K : ℤ) ^ 2 + 2 * Q + 4 * (72 + (H : ℤ) + M) + 2 * K * M := by
    linarith only [hLocal, hJInt, hHighInt]
  dsimp only [E]
  exact_mod_cast hFinal

end

/- Linear-size open packing from a nonlight low. -/
section

/-- The signed neighboring weight is at least the low degree minus the high-vertex count. -/
theorem low_degree_le_neighbor_signed_add_high (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hDegree : ∀ x, G.degree x ≤ q + 2)
    (v : Fin (q ^ 2 + q + 2)) :
    ((lowNeighbors q G v).card : ℤ) ≤
      (∑ x ∈ G.neighborFinset v, signedDeficiency q G x) + (highVertices q G).card := by
  have hEach (x) (hx : x ∈ lowNeighbors q G v) : (1 : ℤ) ≤ signedDeficiency q G x := by
    have h := (Finset.mem_filter.mp hx).2
    omega
  have hSum := Finset.sum_le_sum hEach
  rw [sum_lowNeighbors_deficiency] at hSum
  have hLow : ((lowNeighbors q G v).card : ℤ) ≤ ∑ x ∈ G.neighborFinset v, positiveDeficiency q G x := by
    simpa using hSum
  exact hLow.trans (neighbor_positiveDeficiency_le_signed_add_high q G hDegree v)

/-- The positive row of a low vertex covers its low degree up to the high-vertex count. -/
theorem low_degree_le_positivePartners_add_high (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2) (v : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G v) :
    ((lowNeighbors q G v).card : ℤ) ≤ (positivePartners q G v).card + (highVertices q G).card := by
  have hWeight := low_degree_le_neighbor_signed_add_high q G hDegree v
  have hRow := low_positivePartners_card_lower q G hFree hDegree v hLow
  have hProduct := mul_nonneg (show 0 ≤ signedDeficiency q G v - 1 by omega) (Nat.cast_nonneg (α := ℤ) q)
  have hTriangles : 0 ≤ ∑ x ∈ G.neighborFinset v, (codegree G v x : ℤ) := by positivity
  linarith only [hWeight, hRow, hProduct, hTriangles, hLow]

theorem nonunit_positivePartners_linear (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2) (v : Fin (q ^ 2 + q + 2))
    (hLow : 2 ≤ signedDeficiency q G v) :
    (q : ℤ) ≤ (positivePartners q G v).card + (highVertices q G).card := by
  have hWeight := low_degree_le_neighbor_signed_add_high q G hDegree v
  have hRow := low_positivePartners_card_lower q G hFree hDegree v (by omega)
  have hProduct := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ signedDeficiency q G v - 1 by omega)
    (Nat.cast_nonneg (α := ℤ) q)
  have hTriangles : 0 ≤ ∑ x ∈ G.neighborFinset v, (codegree G v x : ℤ) := by positivity
  have hDelta : (0 : ℤ) ≤ (lowNeighbors q G v).card := by positivity
  simp only [one_mul] at hProduct
  linarith only [hWeight, hRow, hProduct, hTriangles, hLow, hDelta]

theorem heavy_unit_positivePartners_linear (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2) (v : Fin (q ^ 2 + q + 2))
    (hUnit : signedDeficiency q G v = 1)
    (hHeavy : (q : ℤ) ≤ 2 * (triangularRegularNeighbors q G v).card) :
    (q : ℤ) ≤ 2 * ((positivePartners q G v).card + (highVertices q G).card) := by
  have hWeight := low_degree_le_neighbor_signed_add_high q G hDegree v
  have hRow := low_positivePartners_card_lower q G hFree hDegree v (by omega)
  rw [hUnit] at hRow
  have hSubset : triangularRegularNeighbors q G v ⊆ triangularNeighbors G v := by
    intro x hx
    obtain ⟨hxRegular, hxTriangle⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxRegular).1, hxTriangle⟩
  have hTriangles : ((triangularRegularNeighbors q G v).card : ℤ) ≤
      ∑ x ∈ G.neighborFinset v, (codegree G v x : ℤ) := by
    rw [triangle_codegree_sum_eq_card G hFree v]
    exact_mod_cast Finset.card_le_card hSubset
  have hDelta : (0 : ℤ) ≤ (lowNeighbors q G v).card := by positivity
  linarith only [hWeight, hRow, hTriangles, hHeavy, hDelta]

/-- Every bounded-branch nonlight low has a linear-size positive row, allowing for high vertices. -/
theorem bounded_nonlight_positivePartners_linear (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2) (v : Fin (q ^ 2 + q + 2))
    (hv : v ∈ boundedNonlightLowVertices q T G) :
    q ≤ (T + 2) * ((positivePartners q G v).card + (highVertices q G).card) := by
  have hLow : 1 ≤ signedDeficiency q G v := by
    have h := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
    omega
  have hNonneg : (0 : ℤ) ≤ (positivePartners q G v).card + (highVertices q G).card := by positivity
  have hFinal : (q : ℤ) ≤ ((T : ℤ) + 2) * ((positivePartners q G v).card + (highVertices q G).card) := by
    rcases Finset.mem_union.mp (boundedNonlightLowVertices_subset q T G hv) with hHub | hActive
    · have hMany := (Finset.mem_filter.mp hHub).2
      have hRow := low_degree_le_positivePartners_add_high q G hFree hDegree v hLow
      have hScaled := mul_le_mul_of_nonneg_left hRow (Nat.cast_nonneg (α := ℤ) T)
      have hEnlarge := mul_le_mul_of_nonneg_right (show (T : ℤ) ≤ T + 2 by omega) hNonneg
      linarith only [hMany, hScaled, hEnlarge]
    · by_cases hNonunit : 2 ≤ signedDeficiency q G v
      · have hRow := nonunit_positivePartners_linear q G hFree hDegree v hNonunit
        have hEnlarge := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ T + 2 by omega) hNonneg
        simp only [one_mul] at hEnlarge
        exact hRow.trans hEnlarge
      · have hUnit : signedDeficiency q G v = 1 := by omega
        have hHeavy := (Finset.mem_filter.mp hActive).2.resolve_left hNonunit
        have hRow := heavy_unit_positivePartners_linear q G hFree hDegree v hUnit hHeavy
        have hEnlarge := mul_le_mul_of_nonneg_right (show (2 : ℤ) ≤ T + 2 by omega) hNonneg
        exact hRow.trans hEnlarge
  exact_mod_cast hFinal

/-- The zero-codegree neighborhood restricted to bounded-branch nonlight lows. -/
def nonlightZeroNeighbors {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (zeroCodegreeGraph G).neighborFinset v ∩ boundedNonlightLowVertices q T G

/-- Regular, light, and high exceptions account for the positive row outside this neighborhood. -/
theorem positivePartners_le_nonlightZeroNeighbors_add (q T Q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (v : Fin (q ^ 2 + q + 2))
    (hLow : 1 ≤ signedDeficiency q G v)
    (hGood : ((positivePartners q G v).filter fun w => signedDeficiency q G w = 0 ∨
      w ∈ boundedLightLowVertices q T G).card ≤ Q) :
    (positivePartners q G v).card ≤ (nonlightZeroNeighbors q T G v).card + Q + (highVertices q G).card := by
  let R := (positivePartners q G v).filter fun w => signedDeficiency q G w = 0 ∨
    w ∈ boundedLightLowVertices q T G
  have hCover : positivePartners q G v ⊆ nonlightZeroNeighbors q T G v ∪ R ∪ highVertices q G := by
    intro w hw
    by_cases hZero : signedDeficiency q G w = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, Or.inl hZero⟩))
    · by_cases hPos : 0 < signedDeficiency q G w
      · by_cases hLight : w ∈ boundedLightLowVertices q T G
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, Or.inr hLight⟩))
        · obtain ⟨hNe, _hNot, hCodegree⟩ := positivePartner_nonhigh q G v w hLow (by omega) hw
          have hNeighbor : w ∈ (zeroCodegreeGraph G).neighborFinset v :=
            ((zeroCodegreeGraph G).mem_neighborFinset v w).mpr ⟨hNe, hCodegree⟩
          have hNL : w ∈ boundedNonlightLowVertices q T G := Finset.mem_sdiff.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPos⟩, hLight⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hNeighbor, hNL⟩))
      · exact Finset.mem_union_right _ ((mem_highVertices_iff q G w).mpr (by omega))
  have hCard := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hFirst := Finset.card_union_le (nonlightZeroNeighbors q T G v) R
  change R.card ≤ Q at hGood
  omega

/-- Nonlight lows have linearly many zero-codegree partners among the nonlight lows. -/
theorem bounded_nonlight_zero_degree_linear (q T Q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2)
    (hRows : ∀ v, 1 ≤ signedDeficiency q G v →
      ((positivePartners q G v).filter fun w => signedDeficiency q G w = 0 ∨
        w ∈ boundedLightLowVertices q T G).card ≤ Q)
    (hq : 2 * (T + 2) * (Q + 2 * (highVertices q G).card) ≤ q)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ boundedNonlightLowVertices q T G) :
    q ≤ 2 * (T + 2) * (nonlightZeroNeighbors q T G v).card := by
  have hLow : 1 ≤ signedDeficiency q G v := by
    have h := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
    omega
  have hPositive := bounded_nonlight_positivePartners_linear q T G hFree hDegree v hv
  have hCover := positivePartners_le_nonlightZeroNeighbors_add q T Q G v hLow (hRows v hLow)
  have hScaled := Nat.mul_le_mul_left (T + 2) (show (positivePartners q G v).card + (highVertices q G).card ≤
      (nonlightZeroNeighbors q T G v).card + (Q + 2 * (highVertices q G).card) by omega)
  have hAll := hPositive.trans hScaled
  nlinarith only [hAll, hq]

/-- A finite two-color Ramsey bound with an explicit exponential threshold. -/
theorem finite_ramsey_clique {α : Type*} [DecidableEq α] (G : SimpleGraph α) (r s : ℕ) :
    ∀ S : Finset α, 2 ^ (r + s) ≤ S.card →
      (∃ C ⊆ S, G.IsClique (C : Set α) ∧ C.card = r) ∨
      (∃ C ⊆ S, (Gᶜ).IsClique (C : Set α) ∧ C.card = s) := by
  induction r generalizing s with
  | zero =>
      intro S _
      exact Or.inl ⟨∅, Finset.empty_subset S, by simp, rfl⟩
  | succ r ihr =>
      induction s with
      | zero =>
          intro S _
          exact Or.inr ⟨∅, Finset.empty_subset S, by simp, rfl⟩
      | succ s ihs =>
          intro S hSize
          have hPos : 0 < S.card := lt_of_lt_of_le (by positivity : 0 < 2 ^ (r + 1 + (s + 1))) hSize
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hPos
          let A := S.filter (G.Adj v)
          let D := S.erase v \ A
          have hAS : A ⊆ S := Finset.filter_subset _ _
          have hvA : v ∉ A := by simp [A]
          have hAE : A ⊆ S.erase v := by
            intro w hw
            exact Finset.mem_erase.mpr ⟨(G.ne_of_adj (Finset.mem_filter.mp hw).2).symm, hAS hw⟩
          have hDS : D ⊆ S := fun _ hw => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).2
          have hPartition := Finset.card_sdiff_add_card_eq_card hAE
          have hErase := Finset.card_erase_add_one hv
          change D.card + A.card = (S.erase v).card at hPartition
          have hPower : 2 ^ (r + 1 + (s + 1)) = 2 * 2 ^ (r + (s + 1)) := by
            rw [show r + 1 + (s + 1) = r + (s + 1) + 1 by omega, pow_succ]
            omega
          by_cases hA : 2 ^ (r + (s + 1)) ≤ A.card
          · rcases ihr (s + 1) A hA with ⟨C, hCA, hClique, hCard⟩ | ⟨C, hCA, hClique, hCard⟩
            · have hvC : v ∉ C := fun h => hvA (hCA h)
              refine Or.inl ⟨insert v C, Finset.insert_subset hv (hCA.trans hAS), ?_, ?_⟩
              · rw [Finset.coe_insert]
                exact hClique.insert (fun w hw _ => (Finset.mem_filter.mp (hCA hw)).2)
              · rw [Finset.card_insert_of_notMem hvC, hCard]
            · exact Or.inr ⟨C, hCA.trans hAS, hClique, hCard⟩
          · have hD : 2 ^ (r + 1 + s) ≤ D.card := by
              rw [show r + 1 + s = r + (s + 1) by omega]
              omega
            rcases ihs D hD with ⟨C, hCD, hClique, hCard⟩ | ⟨C, hCD, hClique, hCard⟩
            · exact Or.inl ⟨C, hCD.trans hDS, hClique, hCard⟩
            · have hvC : v ∉ C := by
                intro h
                exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp (hCD h)).1).1 rfl
              refine Or.inr ⟨insert v C, Finset.insert_subset hv (hCD.trans hDS), ?_, ?_⟩
              · rw [Finset.coe_insert]
                apply hClique.insert
                intro w hw hNe
                refine ⟨hNe, ?_⟩
                intro hAdj
                have hwD := hCD hw
                exact (Finset.mem_sdiff.mp hwD).2 (Finset.mem_filter.mpr ⟨hDS hwD, hAdj⟩)
              · rw [Finset.card_insert_of_notMem hvC, hCard]

/-- Every finite vertex set has a clique of maximum cardinality within that set. -/
theorem exists_maximum_clique_in_finset {α : Type*} [DecidableEq α] (G : SimpleGraph α) (S : Finset α) :
    ∃ C ⊆ S, G.IsClique (C : Set α) ∧
      ∀ D ⊆ S, G.IsClique (D : Set α) → D.card ≤ C.card := by
  let F := S.powerset.filter fun (C : Finset α) => G.IsClique (C : Set α)
  have hF : F.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset S), by simp⟩⟩
  obtain ⟨C, hC, hMax⟩ := Finset.exists_max_image F Finset.card hF
  obtain ⟨hCS, hClique⟩ := Finset.mem_filter.mp hC
  refine ⟨C, Finset.mem_powerset.mp hCS, hClique, ?_⟩
  intro D hDS hD
  exact hMax D (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hDS, hD⟩)

/-- A vertex outside a maximum clique has few neighbors in it when nonedges have bounded codegree. -/
theorem maximum_clique_outside_neighbors_le {n : ℕ} (G : SimpleGraph (Fin n))
    (S C : Finset (Fin n)) (hCS : C ⊆ S) (hClique : G.IsClique (C : Set (Fin n)))
    (hMax : ∀ D ⊆ S, G.IsClique (D : Set (Fin n)) → D.card ≤ C.card)
    (E : ℕ) (hCommon : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬G.Adj v w → codegree G v w ≤ E)
    (v : Fin n) (hvS : v ∈ S) (hvC : v ∉ C) : (G.neighborFinset v ∩ C).card ≤ E := by
  have hMissing : ∃ w ∈ C, ¬G.Adj v w := by
    by_contra h
    push Not at h
    have hInsert : G.IsClique ((insert v C : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert]
      exact hClique.insert (fun w hw _ => h w hw)
    have hBound := hMax (insert v C) (Finset.insert_subset hvS hCS) hInsert
    rw [Finset.card_insert_of_notMem hvC] at hBound
    omega
  obtain ⟨w, hwC, hNot⟩ := hMissing
  have hNe : v ≠ w := fun h => hvC (h ▸ hwC)
  have hSubset : G.neighborFinset v ∩ C ⊆ G.neighborFinset v ∩ G.neighborFinset w := by
    intro x hx
    obtain ⟨hxN, hxC⟩ := Finset.mem_inter.mp hx
    have hWX : w ≠ x := by
      intro h
      subst x
      exact hNot ((G.mem_neighborFinset v w).mp hxN)
    exact Finset.mem_inter.mpr ⟨hxN, (G.mem_neighborFinset w x).mpr (hClique hwC hxC hWX)⟩
  exact (Finset.card_le_card hSubset).trans (hCommon v hvS w (hCS hwC) hNe hNot)

/-- A sufficiently large maximum clique must have linear size under a minimum-degree and nonedge-codegree bound. -/
theorem maximum_clique_linear_size {n : ℕ} (G : SimpleGraph (Fin n))
    (S C : Finset (Fin n)) (hCS : C ⊆ S) (hClique : G.IsClique (C : Set (Fin n)))
    (hMax : ∀ D ⊆ S, G.IsClique (D : Set (Fin n)) → D.card ≤ C.card)
    (q B E : ℕ) (hSize : S.card ≤ 3 * q)
    (hMin : ∀ v ∈ S, q ≤ B * (G.neighborFinset v ∩ S).card)
    (hCommon : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬G.Adj v w → codegree G v w ≤ E)
    (hLarge : 6 * B * E + 1 ≤ C.card) : q ≤ 2 * B * C.card := by
  have hLower : q * C.card ≤ B * ∑ v ∈ C, (G.neighborFinset v ∩ S).card := by
    calc
      q * C.card = ∑ _v ∈ C, q := by simp [mul_comm]
      _ ≤ ∑ v ∈ C, B * (G.neighborFinset v ∩ S).card :=
        Finset.sum_le_sum (fun v hv => hMin v (hCS hv))
      _ = B * ∑ v ∈ C, (G.neighborFinset v ∩ S).card := by rw [Finset.mul_sum]
  have hInside : (∑ v ∈ C, (G.neighborFinset v ∩ C).card) ≤ C.card ^ 2 := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ C) => Finset.card_le_card (Finset.inter_subset_right
      (s₁ := G.neighborFinset v) (s₂ := C)))
    simpa [pow_two] using h
  have hRest : (∑ v ∈ S \ C, (G.neighborFinset v ∩ C).card) ≤ E * (S \ C).card := by
    have h := Finset.sum_le_sum (fun v (hv : v ∈ S \ C) => maximum_clique_outside_neighbors_le G S C hCS hClique
      hMax E hCommon v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2)
    simpa [mul_comm] using h
  have hPartition := Finset.sum_sdiff (f := fun v => (G.neighborFinset v ∩ C).card) hCS
  have hUpper : (∑ v ∈ S, (G.neighborFinset v ∩ C).card) ≤ C.card ^ 2 + E * S.card := by
    have hRestSize := Nat.mul_le_mul_left E (Finset.card_le_card (Finset.sdiff_subset : S \ C ⊆ S))
    omega
  rw [sum_neighbor_intersection_card G C S] at hLower
  have hUpperScaled := Nat.mul_le_mul_left B hUpper
  have hSizeScaled := Nat.mul_le_mul_left (B * E) hSize
  have hProduct : q * C.card ≤ B * C.card ^ 2 + 3 * B * E * q := by
    nlinarith only [hLower, hUpperScaled, hSizeScaled]
  have hGap : 6 * B * E * q ≤ C.card * q := by
    have h := Nat.mul_le_mul_right q (show 6 * B * E ≤ C.card by omega)
    exact h
  have hProductInt : (q : ℤ) * C.card ≤ (B : ℤ) * C.card ^ 2 + 3 * B * E * q := by exact_mod_cast hProduct
  have hGapInt : 6 * (B : ℤ) * E * q ≤ (C.card : ℤ) * q := by exact_mod_cast hGap
  have hp : (0 : ℤ) < C.card := by exact_mod_cast (show 0 < C.card by omega)
  have hFinal : (q : ℤ) ≤ 2 * B * C.card := by
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith only [hProductInt, hGapInt]
  exact_mod_cast hFinal

/-- Independent sets are bounded by the intersection count when every vertex has many neighbors. -/
theorem sparse_nonedge_independent_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (S I : Finset (Fin n)) (hIS : I ⊆ S) (hIndependent : (Gᶜ).IsClique (I : Set (Fin n)))
    (q B E : ℕ) (hq : 0 < q) (hB : 1 ≤ B) (hSize : S.card ≤ 3 * q)
    (hMin : ∀ v ∈ S, q ≤ B * (G.neighborFinset v ∩ S).card)
    (hCommon : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬G.Adj v w → codegree G v w ≤ E)
    (hGap : 6 * B ^ 2 * E ≤ q) : I.card ≤ 18 * B ^ 2 := by
  have hBound : (I.card : ℤ) ≤ 18 * (B : ℤ) ^ 2 := by
    apply finite_family_card_le I S (fun v => G.neighborFinset v ∩ S) q B E
      (by exact_mod_cast hq) (by exact_mod_cast hB) (Nat.cast_nonneg E)
    · intro v _
      exact Finset.inter_subset_right
    · exact_mod_cast hSize
    · intro v hv
      exact_mod_cast hMin v (hIS hv)
    · intro v hv w hw hNe
      have hNot : ¬G.Adj v w := (hIndependent hv hw hNe).2
      have hSubset : (G.neighborFinset v ∩ S) ∩ (G.neighborFinset w ∩ S) ⊆
          G.neighborFinset v ∩ G.neighborFinset w := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
      have hCard : ((G.neighborFinset v ∩ S ∩ (G.neighborFinset w ∩ S)).card : ℤ) ≤
          (G.neighborFinset v ∩ G.neighborFinset w).card := by exact_mod_cast Finset.card_le_card hSubset
      exact hCard.trans (by exact_mod_cast hCommon v (hIS hv) w (hIS hw) hNe hNot)
    · exact_mod_cast hGap
  exact_mod_cast hBound

/-- A Ramsey seed grows to a linear-size maximum clique under the same hypotheses. -/
theorem exists_linear_maximum_clique {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hNonempty : S.Nonempty)
    (q B E : ℕ) (hq : 0 < q) (hB : 1 ≤ B) (hSize : S.card ≤ 3 * q)
    (hMin : ∀ v ∈ S, q ≤ B * (G.neighborFinset v ∩ S).card)
    (hCommon : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬G.Adj v w → codegree G v w ≤ E)
    (hGap : 6 * B ^ 2 * E ≤ q)
    (hRamsey : B * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) ≤ q) :
    ∃ C ⊆ S, G.IsClique (C : Set (Fin n)) ∧ q ≤ 2 * B * C.card ∧
      (∀ D ⊆ S, G.IsClique (D : Set (Fin n)) → D.card ≤ C.card) ∧
      ∀ v ∈ S, v ∉ C → (G.neighborFinset v ∩ C).card ≤ E := by
  obtain ⟨v, hv⟩ := hNonempty
  have hVertices := (hMin v hv).trans (Nat.mul_le_mul_left B (Finset.card_le_card Finset.inter_subset_right))
  have hSeedSize : 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) ≤ S.card := by
    have hInt : (B : ℤ) * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) ≤ (B : ℤ) * S.card := by
      exact_mod_cast hRamsey.trans hVertices
    have hBPos : (0 : ℤ) < B := by exact_mod_cast (show 0 < B by omega)
    exact_mod_cast (mul_le_mul_iff_of_pos_left hBPos).mp hInt
  have hSeed : ∃ D ⊆ S, G.IsClique (D : Set (Fin n)) ∧ D.card = 6 * B * E + 1 := by
    rcases finite_ramsey_clique G (6 * B * E + 1) (18 * B ^ 2 + 1) S hSeedSize with hClique | hIndependent
    · exact hClique
    · obtain ⟨I, hIS, hI, hCard⟩ := hIndependent
      have hBound := sparse_nonedge_independent_card_le G S I hIS hI q B E hq hB hSize hMin hCommon hGap
      omega
  obtain ⟨D, hDS, hD, hDCard⟩ := hSeed
  obtain ⟨C, hCS, hC, hMax⟩ := exists_maximum_clique_in_finset G S
  have hLarge : 6 * B * E + 1 ≤ C.card := by simpa only [hDCard] using hMax D hDS hD
  refine ⟨C, hCS, hC, maximum_clique_linear_size G S C hCS hC hMax q B E hSize hMin hCommon hLarge, hMax, ?_⟩
  intro w hw hNot
  exact maximum_clique_outside_neighbors_le G S C hCS hC hMax E hCommon w hw hNot

/-- Low zero-codegree partners lie in the positive row or the original low neighborhood. -/
theorem low_zero_neighbors_card_le (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (v : Fin (q ^ 2 + q + 2)) :
    ((zeroCodegreeGraph G).neighborFinset v ∩ lowVertices q G).card ≤
      (positivePartners q G v).card + (lowNeighbors q G v).card := by
  have hCover : (zeroCodegreeGraph G).neighborFinset v ∩ lowVertices q G ⊆
      positivePartners q G v ∪ lowNeighbors q G v := by
    intro w hw
    obtain ⟨hwZero, hwLow⟩ := Finset.mem_inter.mp hw
    obtain ⟨hNe, hCodegree⟩ := ((zeroCodegreeGraph G).mem_neighborFinset v w).mp hwZero
    by_cases hAdj : G.Adj v w
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset v w).mpr hAdj, (Finset.mem_filter.mp hwLow).2⟩)
    · have hEntry := weightedResidual_nonadj q G v w hNe hAdj
      rw [hCodegree] at hEntry
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  exact (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)

/-- If every low is light, a high vertex forces a bounded graph parameter. -/
theorem all_lows_light_high_order_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ x, G.degree x ≤ q + 2)
    (hAll : ∀ x ∈ lowVertices q G, x ∈ boundedLightLowVertices q T G)
    (hIndependent : ∀ x ∈ boundedLightLowVertices q T G, ∀ y ∈ boundedLightLowVertices q T G, ¬G.Adj x y)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ highVertices q G) :
    q ≤ (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + 4 := by
  have hNeg := (mem_highVertices_iff q G v).mp hv
  have hLower := signedDeficiency_ge_neg_one q G hDegree v
  have hDef : signedDeficiency q G v = -1 := by omega
  have hDegreeV : G.degree v = q + 2 := by unfold signedDeficiency at hDef; omega
  have hLowUnit (x) (hx : x ∈ lowNeighbors q G v) : signedDeficiency q G x = 1 := by
    have hxLow : x ∈ lowVertices q G := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    exact (Finset.mem_filter.mp (hAll x hxLow)).2.1
  have hPositive : (∑ x ∈ G.neighborFinset v, positiveDeficiency q G x) = (lowNeighbors q G v).card := by
    rw [← sum_lowNeighbors_deficiency]
    calc
      _ = ∑ _x ∈ lowNeighbors q G v, (1 : ℤ) := Finset.sum_congr rfl hLowUnit
      _ = _ := by simp
  have hMany := high_vertex_positive_neighbor_sum q G hFree v (by omega)
  rw [hPositive] at hMany
  have hSigned : (∑ x ∈ G.neighborFinset v, signedDeficiency q G x) ≤ (lowNeighbors q G v).card := by
    rw [← hPositive]
    exact Finset.sum_le_sum (fun _ _ => le_max_left _ _)
  have hZero := zeroCodegree_degree_identity q G hFree v
  rw [hDef] at hZero
  have hLowCount : (lowNeighbors q G v).card ≤ q + 2 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using le_of_eq hDegreeV)
  have hLowCountInt : ((lowNeighbors q G v).card : ℤ) ≤ q + 2 := by exact_mod_cast hLowCount
  have hZeroSmall : ((zeroCodegreeGraph G).degree v : ℤ) ≤ 3 := by
    linarith only [hZero, hSigned, hLowCountInt]
  have hEmpty : boundedNonlightLowVertices q T G = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxLow, hxNot⟩ := Finset.mem_sdiff.mp hx
    exact hxNot (hAll x hxLow)
  have hTriangles := bounded_triangular_light_neighbor_card_le q T G hFree hIndependent v
  rw [hEmpty, Finset.inter_empty, Finset.card_empty, add_zero] at hTriangles
  have hCover : lowNeighbors q G v ⊆ (zeroCodegreeGraph G).neighborFinset v ∪ boundedTriangularLightNeighbors q T G v := by
    intro x hx
    have hAdj := (G.mem_neighborFinset v x).mp (Finset.mem_filter.mp hx).1
    have hxLow : x ∈ lowVertices q G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    by_cases hZero : codegree G v x = 0
    · exact Finset.mem_union_left _ (((zeroCodegreeGraph G).mem_neighborFinset v x).mpr ⟨hAdj.ne, hZero⟩)
    · have hOne : codegree G v x = 1 := by
        have h := codegree_le_one G hFree v x hAdj.ne
        omega
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hAll x hxLow, hOne⟩)
  have hCard := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hCard
  have hCardInt : ((lowNeighbors q G v).card : ℤ) ≤ (zeroCodegreeGraph G).degree v +
      (boundedTriangularLightNeighbors q T G v).card := by exact_mod_cast hCard
  have hTrianglesInt : ((boundedTriangularLightNeighbors q T G v).card : ℤ) ≤
      (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card := by exact_mod_cast hTriangles
  have hFinal : (q : ℤ) ≤ (boundedLightTriangleRegularVertices q T G).card + (highVertices q G).card + 4 := by
    linarith only [hMany, hZeroSmall, hCardInt, hTrianglesInt]
  exact_mod_cast hFinal

/-- A zero-codegree clique is an open packing of the original graph. -/
theorem zeroCodegree_clique_open_packing {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hP : (zeroCodegreeGraph G).IsClique (P : Set (Fin n))) :
    ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  intro v hv w hw hNe
  have hCodegree := (hP hv hw hNe).2
  exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hCodegree)

/-- Quantitative light bounds and a nonlight vertex give a maximum low open packing. -/
theorem exists_open_packing_of_bounded_light (q T B R M Q E : ℕ) (hBDef : B = 2 * (T + 2))
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hIndependent : ∀ v ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj v w)
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hLights : ∀ v ∈ boundedLightLowVertices q T G, (positivePartners q G v).card ≤ R)
    (hRows : ∀ v, 1 ≤ signedDeficiency q G v →
      ((positivePartners q G v).filter fun w => signedDeficiency q G w = 0 ∨ w ∈ boundedLightLowVertices q T G).card ≤ Q)
    (hLowSize : (lowVertices q G).card ≤ 3 * q)
    (hCommonL : ∀ v ∈ lowVertices q G, ∀ w ∈ lowVertices q G, v ≠ w →
      ¬(zeroCodegreeGraph G).Adj v w → codegree (zeroCodegreeGraph G) v w ≤ E)
    (hRowsActual : 2 * (T + 2) * (Q + 2 * (highVertices q G).card) ≤ q)
    (hGap : 6 * B ^ 2 * E ≤ q)
    (hRamsey : B * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) ≤ q)
    (hLightOrder : 2 * B * (R + M + 2) ≤ q)
    (hNonempty : (boundedNonlightLowVertices q T G).Nonempty) :
    ∃ P : Finset (Fin (q ^ 2 + q + 2)), P ⊆ boundedNonlightLowVertices q T G ∧
      (zeroCodegreeGraph G).IsClique (P : Set _) ∧ q ≤ 2 * B * P.card ∧
      (∀ A ⊆ lowVertices q G, (zeroCodegreeGraph G).IsClique (A : Set _) → A.card ≤ P.card) ∧
      (∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) ∧
      ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  let D := 2 * B
  change D * (R + M + 2) ≤ q at hLightOrder
  let S := boundedNonlightLowVertices q T G
  let L := lowVertices q G
  have hB : 1 ≤ B := by omega
  have hD : 1 ≤ D := by dsimp only [D]; omega
  have hq : 0 < q := by
    have hPositive : 0 < B * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) := by positivity
    omega
  have hSL : S ⊆ L := Finset.sdiff_subset
  have hSize : S.card ≤ 3 * q := (Finset.card_le_card hSL).trans hLowSize
  have hMinS (v) (hv : v ∈ S) : q ≤ B * ((zeroCodegreeGraph G).neighborFinset v ∩ S).card := by
    rw [hBDef]
    exact bounded_nonlight_zero_degree_linear q T Q G hFree hDegree hRows hRowsActual v hv
  obtain ⟨C, hCS, hCliqueC, hCSize, _hMaxC, _hOutsideC⟩ := exists_linear_maximum_clique (zeroCodegreeGraph G)
    S hNonempty q B E hq hB hSize hMinS (fun v hv w hw => hCommonL v (hSL hv) w (hSL hw)) hGap hRamsey
  obtain ⟨P, hPL, hCliqueP, hMaxP⟩ := exists_maximum_clique_in_finset (zeroCodegreeGraph G) L
  have hCP := hMaxP C (hCS.trans hSL) hCliqueC
  have hPSize : q ≤ D * P.card := by
    change q ≤ D * C.card at hCSize
    exact hCSize.trans (Nat.mul_le_mul_left D hCP)
  have hPS : P ⊆ S := by
    intro v hv
    have hvLow := hPL hv
    have hvNotLight : v ∉ boundedLightLowVertices q T G := by
      intro hvLight
      have hRow := hLights v hvLight
      change (positivePartners q G v).card ≤ R at hRow
      have hLowDegree : (lowNeighbors q G v).card ≤ M := by
        rw [bounded_light_lowNeighbors_eq_nonlight q T G hIndependent v hvLight]
        exact hNonlight v
      have hZero := low_zero_neighbors_card_le q G v
      change ((zeroCodegreeGraph G).neighborFinset v ∩ L).card ≤
        (positivePartners q G v).card + (lowNeighbors q G v).card at hZero
      have hErase : P.erase v ⊆ (zeroCodegreeGraph G).neighborFinset v ∩ L := by
        intro w hw
        obtain ⟨hwNe, hwP⟩ := Finset.mem_erase.mp hw
        exact Finset.mem_inter.mpr
          ⟨((zeroCodegreeGraph G).mem_neighborFinset v w).mpr (hCliqueP hv hwP hwNe.symm), hPL hwP⟩
      have hCard := Finset.card_le_card hErase
      have hPartition := Finset.card_erase_add_one hv
      have hSmall : P.card ≤ R + M + 1 := by omega
      have hScaled := Nat.mul_le_mul_left D hSmall
      have hStrict : D * (R + M + 1) < D * (R + M + 2) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    exact Finset.mem_sdiff.mpr ⟨hvLow, hvNotLight⟩
  refine ⟨P, hPS, hCliqueP, hPSize, hMaxP, ?_, zeroCodegree_clique_open_packing G P hCliqueP⟩
  intro v hv hNot
  exact maximum_clique_outside_neighbors_le (zeroCodegreeGraph G) L P hPL hCliqueP hMaxP E hCommonL v hv hNot

/-- The bounded-branch estimates yield a linear-size maximum open packing once a nonlight low exists. -/
theorem claimedBound_uniform_open_packing_of_nonlight (hBound : ClaimedBound) :
    ∃ T D E N : ℕ, 1 ≤ D ∧ ∀ r : ℕ, N ≤ 2 ^ r →
      ∀ G : SimpleGraph (Fin ((2 ^ r) ^ 2 + 2 ^ r + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ r) ^ 2 + 2 ^ r + 2) (cycleGraph 4) →
        (boundedNonlightLowVertices (2 ^ r) T G).Nonempty →
        ∃ P : Finset (Fin ((2 ^ r) ^ 2 + 2 ^ r + 2)),
          P ⊆ boundedNonlightLowVertices (2 ^ r) T G ∧
          (zeroCodegreeGraph G).IsClique (P : Set _) ∧ 2 ^ r ≤ D * P.card ∧
          (∀ A ⊆ lowVertices (2 ^ r) G, (zeroCodegreeGraph G).IsClique (A : Set _) → A.card ≤ P.card) ∧
          (∀ v ∈ lowVertices (2 ^ r) G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) ∧
          ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  obtain ⟨_C, _K, T, M, R, Q, _hC, _hK, N₀, hStructure⟩ := claimedBound_uniform_light_structure hBound
  obtain ⟨C₀, hC₀, N₁, hPrep⟩ := claimedBound_uniform_preparation hBound
  obtain ⟨E, N₂, hCommon⟩ := claimedBound_uniform_common_zeroCodegree hBound
  let H := 2611456 * C₀
  let B := 2 * (T + 2)
  let D := 2 * B
  let cutoff := N₀ + N₁ + N₂ + 48 * C₀ + H + 1 +
    2 * (T + 2) * (Q + 2 * H) + 6 * B ^ 2 * E +
    B * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) + D * (R + M + 2)
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hD : 1 ≤ D := by dsimp only [D]; omega
  refine ⟨T, D, E, cutoff, hD, ?_⟩
  intro r hr G hFree hEdges hNonempty
  let q := 2 ^ r
  let L := lowVertices q G
  have hCutoff : cutoff ≤ q := hr
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₁ : N₁ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₂ : N₂ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have h48 : 48 * C₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHq : H ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hRowsOrder : 2 * (T + 2) * (Q + 2 * H) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hGap : 6 * B ^ 2 * E ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hRamsey : B * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) ≤ q := by
    dsimp only [cutoff] at hCutoff; omega
  have hLightOrder : D * (R + M + 2) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  obtain ⟨_hGlobal, hIndependent, hNonlight, hLights, _hJ, _hRegular, hRows⟩ := hStructure r hN₀ G hFree hEdges
  obtain ⟨hExcess, hGraphs⟩ := hPrep r hN₁
  obtain ⟨_hNoCheap, _hMin, hDegree, hHigh, _hPositive⟩ := hGraphs G hFree hEdges
  change q ≤ 4 * C₀ * abovePlaneExcess q ^ 2 at hExcess
  change (∀ v, G.degree v ≤ q + 2) at hDegree
  change (highVertices q G).card ≤ H at hHigh
  have hExcessThree : 3 ≤ abovePlaneExcess q := by
    by_contra h
    have hSmall : abovePlaneExcess q ≤ 2 := by omega
    have hSquare : abovePlaneExcess q ^ 2 ≤ 4 := by nlinarith only [hSmall]
    have hProduct := Nat.mul_le_mul_left (4 * C₀) hSquare
    omega
  have hDense := extremal_density_of_excess q G hEdges hExcessThree
  have hLowSize : L.card ≤ 3 * q := by
    exact_mod_cast dense_lowVertices_card_le q G hDegree hDense (hHigh.trans hHq)
  have hCommonL (v) (hv : v ∈ L) (w) (hw : w ∈ L) (hNe : v ≠ w)
      (hNot : ¬(zeroCodegreeGraph G).Adj v w) : codegree (zeroCodegreeGraph G) v w ≤ E := by
    have hNZ : codegree G v w ≠ 0 := fun hz => hNot ⟨hNe, hz⟩
    have hOne : codegree G v w = 1 := by
      have hUpper := codegree_le_one G hFree v w hNe
      omega
    have hV : 1 ≤ signedDeficiency q G v := by have h := (Finset.mem_filter.mp hv).2; omega
    have hW : 1 ≤ signedDeficiency q G w := by have h := (Finset.mem_filter.mp hw).2; omega
    exact hCommon r hN₂ G hFree hEdges v w hNe hOne hV hW
  have hRowsActual : 2 * (T + 2) * (Q + 2 * (highVertices q G).card) ≤ q := by
    calc
      _ ≤ 2 * (T + 2) * (Q + 2 * H) := by gcongr
      _ ≤ _ := hRowsOrder
  exact exists_open_packing_of_bounded_light q T B R M Q E rfl G hFree hDegree hIndependent hNonlight
    (fun v hv => (hLights v hv).2) hRows hLowSize hCommonL hRowsActual hGap hRamsey hLightOrder hNonempty


end

/- Finite row support and the all-light residual involution. -/
section

/-- A nonunit natural number is covered by twice its unordered pair count. -/
theorem le_two_mul_choose_two_of_ne_one (m : ℕ) (hm : m ≠ 1) :
    m ≤ 2 * m.choose 2 := by
  cases m with
  | zero => simp
  | succ m =>
      cases m with
      | zero => omega
      | succ k =>
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          omega

/-- If every outside vertex meets a nonempty set in zero or at least two points, its minimum degree is bounded by its size. -/
theorem degree_le_three_mul_card_of_no_single_neighbor {n : ℕ}
    (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G)
    (S : Finset (Fin n)) (hS : S.Nonempty) (q : ℕ)
    (hMin : ∀ v ∈ S, q ≤ G.degree v)
    (hNoOne : ∀ v, v ∉ S → (G.neighborFinset v ∩ S).card ≠ 1) :
    q ≤ 3 * S.card := by
  let O := Finset.univ \ S
  have hInside : (∑ v ∈ S, (G.neighborFinset v ∩ S).card) ≤ S.card ^ 2 := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ S) => Finset.card_le_card
      (Finset.inter_subset_right : G.neighborFinset v ∩ S ⊆ S))
    simpa [pow_two] using h
  have hOutside : (∑ v ∈ O, (G.neighborFinset v ∩ S).card) ≤ 2 * S.card ^ 2 := by
    calc
      _ ≤ ∑ v ∈ O, 2 * ((G.neighborFinset v ∩ S).card).choose 2 := by
        apply Finset.sum_le_sum
        intro v hv
        exact le_two_mul_choose_two_of_ne_one _ (hNoOne v (Finset.mem_sdiff.mp hv).2)
      _ = 2 * ∑ v ∈ O, ((G.neighborFinset v ∩ S).card).choose 2 := by rw [Finset.mul_sum]
      _ ≤ 2 * S.card.choose 2 := Nat.mul_le_mul_left 2 (sum_choose_neighbors_in_set_le G hFree O S)
      _ ≤ 2 * S.card ^ 2 := Nat.mul_le_mul_left 2 (Nat.choose_le_pow S.card 2)
  have hPartition := Finset.sum_sdiff
    (f := fun v => (G.neighborFinset v ∩ S).card) (Finset.subset_univ S)
  change (∑ v ∈ O, (G.neighborFinset v ∩ S).card) +
    (∑ v ∈ S, (G.neighborFinset v ∩ S).card) = _ at hPartition
  have hCount : (∑ v, (G.neighborFinset v ∩ S).card) = ∑ v ∈ S, G.degree v := by
    simpa only [Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree]
      using sum_neighbor_intersection_card G Finset.univ S
  have hLower : q * S.card ≤ ∑ v ∈ S, G.degree v := by
    have h : (∑ _v ∈ S, q) ≤ ∑ v ∈ S, G.degree v := Finset.sum_le_sum hMin
    simpa [mul_comm] using h
  have hProduct : q * S.card ≤ 3 * S.card ^ 2 := by omega
  have hProductInt : (q : ℤ) * S.card ≤ 3 * (S.card : ℤ) ^ 2 := by exact_mod_cast hProduct
  have hPositive : (0 : ℤ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hFinal : (q : ℤ) ≤ 3 * S.card := by
    apply (mul_le_mul_iff_of_pos_right hPositive).mp
    nlinarith only [hProductInt]
  exact_mod_cast hFinal

/-- Rows that contain a nonzero entry of a matrix. -/
def matrixRowSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ w, M v w ≠ 0

theorem matrixRowSupport_not_mem_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) :
    v ∉ matrixRowSupport M ↔ ∀ w, M v w = 0 := by
  simp [matrixRowSupport]

/-- Commutation makes the sum of neighboring rows vanish at a zero row. -/
theorem commuting_matrix_neighbor_row_sum_zero {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (M : Matrix (Fin n) (Fin n) ℤ)
    (hComm : weightedAdjacency q G * M = M * weightedAdjacency q G)
    (v : Fin n) (hv : v ∉ matrixRowSupport M) (w : Fin n) :
    (∑ x ∈ G.neighborFinset v, M x w) = 0 := by
  have hRow := (matrixRowSupport_not_mem_iff M v).mp hv
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℤ => A v w) hComm
  rw [weightedAdjacency_mul_apply, mul_weightedAdjacency_apply] at h
  simpa only [hRow, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add] using h

/-- A zero row cannot have exactly one graph neighbor with a nonzero row. -/
theorem commuting_matrix_support_no_single_neighbor {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (M : Matrix (Fin n) (Fin n) ℤ)
    (hComm : weightedAdjacency q G * M = M * weightedAdjacency q G)
    (v : Fin n) (hv : v ∉ matrixRowSupport M) :
    (G.neighborFinset v ∩ matrixRowSupport M).card ≠ 1 := by
  intro hOne
  obtain ⟨u, hSet⟩ := Finset.card_eq_one.mp hOne
  have hu : u ∈ G.neighborFinset v ∩ matrixRowSupport M := by rw [hSet]; simp
  obtain ⟨w, hNonzero⟩ := (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2
  have hRestrict : (∑ x ∈ G.neighborFinset v ∩ matrixRowSupport M, M x w) =
      ∑ x ∈ G.neighborFinset v, M x w := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro x hxN hxNot
    have hxSupport : x ∉ matrixRowSupport M := fun h => hxNot (Finset.mem_inter.mpr ⟨hxN, h⟩)
    exact (matrixRowSupport_not_mem_iff M x).mp hxSupport w
  rw [hSet, Finset.sum_singleton] at hRestrict
  exact hNonzero (hRestrict.trans (commuting_matrix_neighbor_row_sum_zero q G M hComm v hv w))

/-- A nonzero commuting matrix forces its row support to be large in a high-minimum-degree C4-free graph. -/
theorem commuting_matrix_support_degree_bound {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G)
    (M : Matrix (Fin n) (Fin n) ℤ) (hNonzero : M ≠ 0)
    (hComm : weightedAdjacency q G * M = M * weightedAdjacency q G)
    (hMin : ∀ v ∈ matrixRowSupport M, q ≤ G.degree v) :
    q ≤ 3 * (matrixRowSupport M).card := by
  have hS : (matrixRowSupport M).Nonempty := by
    by_contra h
    have hEmpty : matrixRowSupport M = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hNonzero
    ext v w
    have hv : v ∉ matrixRowSupport M := by rw [hEmpty]; simp
    exact (matrixRowSupport_not_mem_iff M v).mp hv w
  exact degree_le_three_mul_card_of_no_single_neighbor G hFree (matrixRowSupport M) hS q hMin
    (fun v hv => commuting_matrix_support_no_single_neighbor q G M hComm v hv)

theorem commuting_matrix_eq_zero_of_small_support {n : ℕ} (q : ℕ)
    (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G)
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hComm : weightedAdjacency q G * M = M * weightedAdjacency q G)
    (hMin : ∀ v, q ≤ G.degree v) (hSmall : 3 * (matrixRowSupport M).card < q) : M = 0 := by
  by_contra h
  have hBound := commuting_matrix_support_degree_bound q G hFree M h hComm (fun v _ => hMin v)
  omega

/-- A nonnegative integer row with sum one has one unit entry and all other entries zero. -/
theorem nonnegative_integer_unit_row {n : ℕ} (z : Fin n → ℤ)
    (hNonneg : ∀ v, 0 ≤ z v) (hSum : ∑ v, z v = 1) :
    ∃ u, z u = 1 ∧ ∀ v, v ≠ u → z v = 0 := by
  have hSome : ∃ u, 0 < z u := by
    by_contra h
    push Not at h
    have hBound := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => h v)
    simp only [Finset.sum_const_zero] at hBound
    omega
  obtain ⟨u, hu⟩ := hSome
  have hUpper : z u ≤ ∑ v, z v := Finset.single_le_sum (fun v _ => hNonneg v) (Finset.mem_univ u)
  have hUnit : z u = 1 := by omega
  refine ⟨u, hUnit, ?_⟩
  intro v hv
  have hErase := Finset.sum_erase_add Finset.univ z (Finset.mem_univ u)
  have hRest : (∑ w ∈ Finset.univ.erase u, z w) = 0 := by omega
  have hSingle : z v ≤ ∑ w ∈ Finset.univ.erase u, z w :=
    Finset.single_le_sum (fun w _ => hNonneg w) (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)
  have hZero := hNonneg v
  omega

def matrixNegativeRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ w, M v w < 0

def matrixPositiveRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w => 0 < M v w

def negativeRowsPositiveClosure {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Finset (Fin n) :=
  matrixNegativeRows M ∪ (matrixNegativeRows M).biUnion (fun v => matrixPositiveRow M v)

theorem matrixNegativeRows_not_mem_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) :
    v ∉ matrixNegativeRows M ↔ ∀ w, 0 ≤ M v w := by
  simp only [matrixNegativeRows, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_lt]

/-- Outside the negative rows and their positive neighbors, a symmetric integer unit-row matrix pairs vertices. -/
theorem square_row_eq_one_outside_negative_closure {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (hSymm : M.IsSymm) (hRows : ∀ v, ∑ w, M v w = 1)
    (v : Fin n) (hv : v ∉ negativeRowsPositiveClosure M) :
    ∀ w, (M * M) v w = (1 : Matrix (Fin n) (Fin n) ℤ) v w := by
  have hvNot : v ∉ matrixNegativeRows M := fun h => hv (Finset.mem_union_left _ h)
  obtain ⟨u, hUnit, hZero⟩ := nonnegative_integer_unit_row (M v)
    ((matrixNegativeRows_not_mem_iff M v).mp hvNot) (hRows v)
  have hSymUnit : M u v = 1 := by
    calc
      M u v = M v u := (hSymm.apply u v).symm
      _ = 1 := hUnit
  have huNot : u ∉ matrixNegativeRows M := by
    intro hu
    apply hv
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩⟩
  obtain ⟨z, hzUnit, hzZero⟩ := nonnegative_integer_unit_row (M u)
    ((matrixNegativeRows_not_mem_iff M u).mp huNot) (hRows u)
  have hzv : z = v := by
    by_contra h
    have hZeroV := hzZero v (Ne.symm h)
    omega
  subst z
  have hRow (w) : M u w = (1 : Matrix (Fin n) (Fin n) ℤ) v w := by
    by_cases hw : w = v
    · subst w
      simpa using hzUnit
    · simpa only [Matrix.one_apply, ite_eq_right (Ne.symm hw)] using hzZero w hw
  intro w
  rw [Matrix.mul_apply]
  calc
    (∑ x, M v x * M x w) = M v u * M u w := by
      apply Finset.sum_eq_single u
      · intro x _ hxu
        rw [hZero x hxu, zero_mul]
      · intro hu
        exact False.elim (hu (Finset.mem_univ u))
    _ = M u w := by rw [hUnit, one_mul]
    _ = _ := hRow w

theorem square_sub_one_support_subset {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (hSymm : M.IsSymm) (hRows : ∀ v, ∑ w, M v w = 1) :
    matrixRowSupport (M * M - 1) ⊆ negativeRowsPositiveClosure M := by
  intro v hv
  by_contra hNot
  obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hv).2
  have hRow := square_row_eq_one_outside_negative_closure M hSymm hRows v hNot w
  exact hw (by rw [Matrix.sub_apply, hRow, sub_self])

theorem negativeRowsPositiveClosure_card_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (R : ℕ) (hPositive : ∀ v, (matrixPositiveRow M v).card ≤ R) :
    (negativeRowsPositiveClosure M).card ≤ (matrixNegativeRows M).card * (R + 1) := by
  have hUnion := Finset.card_union_le (matrixNegativeRows M)
    ((matrixNegativeRows M).biUnion fun v => matrixPositiveRow M v)
  have hBi := Finset.card_biUnion_le (s := matrixNegativeRows M) (t := fun v => matrixPositiveRow M v)
  have hSum := Finset.sum_le_sum (fun v (_ : v ∈ matrixNegativeRows M) => hPositive v)
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  change (negativeRowsPositiveClosure M).card ≤ _ at hUnion
  nlinarith only [hUnion, hBi, hSum]

theorem commute_square_sub_one {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℤ)
    (hComm : A * M = M * A) : A * (M * M - 1) = (M * M - 1) * A := by
  have hSquare : A * (M * M) = (M * M) * A := by
    rw [← mul_assoc, hComm, mul_assoc, hComm, ← mul_assoc]
  rw [mul_sub, sub_mul, mul_one, one_mul, hSquare]

/-- A small negative-row closure forces a symmetric integer commuting unit-row matrix to be an involution. -/
theorem commuting_unit_row_matrix_square_eq_one {n : ℕ} (q R : ℕ)
    (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G) (hMin : ∀ v, q ≤ G.degree v)
    (M : Matrix (Fin n) (Fin n) ℤ) (hSymm : M.IsSymm) (hRows : ∀ v, ∑ w, M v w = 1)
    (hComm : weightedAdjacency q G * M = M * weightedAdjacency q G)
    (hPositive : ∀ v, (matrixPositiveRow M v).card ≤ R)
    (hSmall : 3 * ((matrixNegativeRows M).card * (R + 1)) < q) : M * M = 1 := by
  have hSupport := Finset.card_le_card (square_sub_one_support_subset M hSymm hRows)
  have hClosure := negativeRowsPositiveClosure_card_le M R hPositive
  have hCard : (matrixRowSupport (M * M - 1)).card ≤ (matrixNegativeRows M).card * (R + 1) :=
    hSupport.trans hClosure
  have hBound := Nat.mul_le_mul_left 3 hCard
  have hZero := commuting_matrix_eq_zero_of_small_support q G hFree (M * M - 1)
    (commute_square_sub_one (weightedAdjacency q G) M hComm) hMin (lt_of_le_of_lt hBound hSmall)
  exact sub_eq_zero.mp hZero

theorem all_lows_light_nonlight_empty {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (hAll : ∀ v ∈ lowVertices q G, v ∈ boundedLightLowVertices q T G) :
    boundedNonlightLowVertices q T G = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvLow, hvNot⟩ := Finset.mem_sdiff.mp hv
  exact hvNot (hAll v hvLow)

theorem nonnegative_deficiency_high_empty {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hNonnegative : ∀ v, 0 ≤ signedDeficiency q G v) : highVertices q G = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hNegative := (mem_highVertices_iff q G v).mp hv
  have h := hNonnegative v
  omega

theorem all_lows_light_deficiency_cases {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (hNonnegative : ∀ v, 0 ≤ signedDeficiency q G v)
    (hAll : ∀ v ∈ lowVertices q G, v ∈ boundedLightLowVertices q T G) (v : Fin n) :
    signedDeficiency q G v = 0 ∨ signedDeficiency q G v = 1 := by
  by_cases hPositive : 0 < signedDeficiency q G v
  · exact Or.inr (Finset.mem_filter.mp (hAll v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPositive⟩))).2.1
  · have h := hNonnegative v
    exact Or.inl (by omega)

/-- Negative residual rows in the all-light case lie near the exceptional regular set. -/
theorem all_lows_light_negative_rows_card_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hNonnegative : ∀ v, 0 ≤ signedDeficiency q G v)
    (hAll : ∀ v ∈ lowVertices q G, v ∈ boundedLightLowVertices q T G)
    (hIndependent : ∀ v ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj v w) :
    (matrixNegativeRows (weightedResidual q G)).card ≤
      (boundedLightTriangleRegularVertices q T G).card + (boundedLightTriangleRegularVertices q T G).card ^ 2 := by
  let J := boundedLightTriangleRegularVertices q T G
  let S := J ∪ J.biUnion (fun v => boundedTriangularLightNeighbors q T G v)
  have hEmpty := all_lows_light_nonlight_empty q T G hAll
  have hHighEmpty := nonnegative_deficiency_high_empty q G hNonnegative
  have hCases := all_lows_light_deficiency_cases q T G hNonnegative hAll
  have hCover : matrixNegativeRows (weightedResidual q G) ⊆ S := by
    intro v hv
    obtain ⟨w, hNegative⟩ := (Finset.mem_filter.mp hv).2
    have hDiagonal : weightedResidual q G v v = 0 := by
      rw [weightedResidual_diagonal]
      rcases hCases v with h | h <;> simp [h]
    have hNe : v ≠ w := by intro h; subst w; omega
    have hReverse : weightedResidual q G w v < 0 := by
      rw [(weightedResidual_symmetric q G).apply v w]
      exact hNegative
    rcases hCases v with hRegular | hUnit
    · have hvJ : v ∈ J := by
        by_contra hNot
        have hBad := bounded_regular_negative_entry_support q T G hFree v w hRegular hNot hNe.symm hReverse
        simp [hEmpty] at hBad
      exact Finset.mem_union_left _ hvJ
    · have hvLight : v ∈ boundedLightLowVertices q T G := hAll v
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      rcases bounded_light_negative_entry_support q T G hFree v w hvLight hNe.symm hReverse with hwLow | hwJ
      · have hwLight := hAll w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwLow).2⟩)
        exact False.elim (hIndependent v hvLight w hwLight
          ((G.mem_neighborFinset v w).mp (Finset.mem_filter.mp hwLow).1))
      · have hAdj : G.Adj v w := by
          by_contra hNot
          have hNonneg := weightedResidual_nonadj_nonnegative q G hFree v w hNe hNot
          omega
        have hwRegular := boundedLightTriangleRegularVertices_regular q T G w hwJ
        have hEntry := weightedResidual_off_diagonal q G v w hNe
        rw [adjMatrix_square_codegree] at hEntry
        simp only [G.adjMatrix_apply, ite_eq_left hAdj, hUnit, hwRegular, add_zero, one_mul] at hEntry
        have hUpper := codegree_le_one G hFree v w hNe
        have hTriangle : codegree G v w = 1 := by omega
        have hvTriangle : v ∈ boundedTriangularLightNeighbors q T G w := Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset w v).mpr hAdj.symm, hvLight, by rw [codegree_symm]; exact hTriangle⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hwJ, hvTriangle⟩)
  have hEach (v) (_ : v ∈ J) : (boundedTriangularLightNeighbors q T G v).card ≤ J.card := by
    have h := bounded_triangular_light_neighbor_card_le q T G hFree hIndependent v
    simpa [hEmpty, hHighEmpty, J] using h
  have hBi := Finset.card_biUnion_le (s := J) (t := fun v => boundedTriangularLightNeighbors q T G v)
  have hSum : (∑ v ∈ J, (boundedTriangularLightNeighbors q T G v).card) ≤ J.card ^ 2 := by
    simpa [pow_two] using Finset.sum_le_sum hEach
  have hCard := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  change _ ≤ J.card + J.card ^ 2
  change _ ≤ J.card + (J.biUnion fun v => boundedTriangularLightNeighbors q T G v).card at hCard
  omega

theorem weightedResidual_sum_row_one (q : ℕ) (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (v : Fin (q ^ 2 + q + 2)) : (∑ w, weightedResidual q G v w) = 1 := by
  have h := congrArg (fun f : Fin (q ^ 2 + q + 2) → ℤ => f v) (weightedResidual_row_sum q G)
  simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one] at h
  push_cast at h
  nlinarith only [h]

theorem all_lows_light_min_degree {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (hAll : ∀ v ∈ lowVertices q G, v ∈ boundedLightLowVertices q T G) (v : Fin n) : q ≤ G.degree v := by
  have hBound : signedDeficiency q G v ≤ 1 := by
    by_cases hPositive : 0 < signedDeficiency q G v
    · have hUnit := (Finset.mem_filter.mp (hAll v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPositive⟩))).2.1
      omega
    · omega
  unfold signedDeficiency at hBound
  omega

/-- The all-light residual matrix is an involution once its negative-row neighborhood is small relative to q. -/
theorem all_lows_light_residual_square_eq_one (q T R : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hNonnegative : ∀ v, 0 ≤ signedDeficiency q G v)
    (hAll : ∀ v ∈ lowVertices q G, v ∈ boundedLightLowVertices q T G)
    (hIndependent : ∀ v ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj v w)
    (hPositive : ∀ v, (positivePartners q G v).card ≤ R)
    (hOrder : 3 * (((boundedLightTriangleRegularVertices q T G).card +
      (boundedLightTriangleRegularVertices q T G).card ^ 2) * (R + 1)) < q) :
    weightedResidual q G * weightedResidual q G = 1 := by
  have hNegative := all_lows_light_negative_rows_card_le q T G hFree hNonnegative hAll hIndependent
  have hScaled := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right (R + 1) hNegative)
  apply commuting_unit_row_matrix_square_eq_one q R G hFree (all_lows_light_min_degree q T G hAll)
    (weightedResidual q G) (weightedResidual_symmetric q G) (weightedResidual_sum_row_one q G)
    (weightedAdjacency_commutes_residual q G)
  · intro v
    simpa only [matrixPositiveRow, positivePartners] using hPositive v
  · exact lt_of_le_of_lt hScaled hOrder

/-- If a prepared dyadic extremizer has no nonlight low, its residual matrix is a rational-involution candidate. -/
theorem claimedBound_uniform_all_light_involution (hBound : ClaimedBound) :
    ∃ T N : ℕ, ∀ r : ℕ, N ≤ 2 ^ r →
      ∀ G : SimpleGraph (Fin ((2 ^ r) ^ 2 + 2 ^ r + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ r) ^ 2 + 2 ^ r + 2) (cycleGraph 4) →
        boundedNonlightLowVertices (2 ^ r) T G = ∅ →
        (∀ v, signedDeficiency (2 ^ r) G v = 0 ∨ signedDeficiency (2 ^ r) G v = 1) ∧
        weightedResidual (2 ^ r) G * weightedResidual (2 ^ r) G = 1 := by
  obtain ⟨_C, _K, T, _M, R, _Q, _hC, _hK, N₀, hStructure⟩ := claimedBound_uniform_light_structure hBound
  obtain ⟨C₀, _hC₀, N₁, hPrep⟩ := claimedBound_uniform_preparation hBound
  let H := 2611456 * C₀
  let cutoff := N₀ + N₁ + H + 77 + 3 * ((72 + 72 ^ 2) * (R + 1)) + 1
  refine ⟨T, cutoff, ?_⟩
  intro r hr G hFree hEdges hEmpty
  let q := 2 ^ r
  change boundedNonlightLowVertices q T G = ∅ at hEmpty
  have hCutoff : cutoff ≤ q := hr
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₁ : N₁ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHighOrder : H + 76 < q := by dsimp only [cutoff] at hCutoff; omega
  have hOrder : 3 * ((72 + 72 ^ 2) * (R + 1)) < q := by dsimp only [cutoff] at hCutoff; omega
  obtain ⟨_hGlobal, hIndependent, _hNonlight, hLights, hJ, hRegular, _hRows⟩ := hStructure r hN₀ G hFree hEdges
  obtain ⟨_hExcess, hGraphs⟩ := hPrep r hN₁
  obtain ⟨_hNoCheap, _hMin, hDegree, hHigh, _hPositive⟩ := hGraphs G hFree hEdges
  change (∀ v, G.degree v ≤ q + 2) at hDegree
  change (highVertices q G).card ≤ H at hHigh
  change (boundedLightTriangleRegularVertices q T G).card ≤ 72 at hJ
  have hAll (v) (hv : v ∈ lowVertices q G) : v ∈ boundedLightLowVertices q T G := by
    by_contra h
    have hvBad : v ∈ boundedNonlightLowVertices q T G := Finset.mem_sdiff.mpr ⟨hv, h⟩
    simp [hEmpty] at hvBad
  have hNonnegative (v) : 0 ≤ signedDeficiency q G v := by
    by_contra h
    have hvHigh : v ∈ highVertices q G := (mem_highVertices_iff q G v).mpr (by omega)
    have hBoundQ := all_lows_light_high_order_le q T G hFree hDegree hAll hIndependent v hvHigh
    omega
  have hCases := all_lows_light_deficiency_cases q T G hNonnegative hAll
  have hRowBound (v) : (positivePartners q G v).card ≤ R := by
    rcases hCases v with hZero | hOne
    · exact hRegular v hZero
    · exact (hLights v (hAll v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))).2
  have hOrderActual : 3 * (((boundedLightTriangleRegularVertices q T G).card +
      (boundedLightTriangleRegularVertices q T G).card ^ 2) * (R + 1)) < q := by
    apply lt_of_le_of_lt _ hOrder
    gcongr
  exact ⟨hCases, all_lows_light_residual_square_eq_one q T R G hFree hNonnegative hAll hIndependent hRowBound hOrderActual⟩

end

/- The rational square obstruction and unconditional square-dyadic packing. -/
section

/-- An odd power of a rational number can be a square only if the number is a square. -/
theorem rational_square_of_odd_power (a b : ℚ) (d : ℕ) (hd : Odd d)
    (hPower : b ^ 2 = a ^ d) : IsSquare a := by
  by_cases ha : a = 0
  · subst a
    exact ⟨0, by norm_num⟩
  obtain ⟨k, hk⟩ := hd
  have hdForm : d = 2 * k + 1 := by omega
  have hRewrite : a ^ d = (a ^ k) ^ 2 * a := by
    rw [hdForm, pow_add, pow_one, Nat.mul_comm 2 k, pow_mul]
  rw [hRewrite] at hPower
  apply (isSquare_iff_exists_sq a).mpr
  refine ⟨b / a ^ k, ?_⟩
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 (pow_ne_zero k ha))).mpr
  nlinarith only [hPower]

/-- A scalar square on an odd-dimensional rational vector space has square scalar. -/
theorem rational_scalar_square_of_odd_finrank {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (T : Module.End ℚ V) (a : ℚ)
    (hSquare : T * T = a • (1 : Module.End ℚ V)) (hOdd : Odd (Module.finrank ℚ V)) : IsSquare a := by
  have hDet := congrArg (fun f : Module.End ℚ V => LinearMap.det f) hSquare
  simp only [map_mul, LinearMap.det_smul, map_one, mul_one] at hDet
  apply rational_square_of_odd_power a (LinearMap.det T) (Module.finrank ℚ V) hOdd
  simpa only [pow_two] using hDet

/-- The same obstruction applies on the range of a commuting rational projection. -/
theorem rational_scalar_square_on_projector {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (B P : Module.End ℚ V) (a : ℚ)
    (hIdem : P * P = P) (hComm : B * P = P * B)
    (hSquare : B * B * P = a • P)
    (hOdd : Odd (Module.finrank ℚ (LinearMap.range P))) : IsSquare a := by
  let S := LinearMap.range P
  have hProj := (LinearMap.IsIdempotentElem.isProj_range P (show IsIdempotentElem P from hIdem))
  have hInvariant (x : V) (hx : x ∈ S) : B x ∈ S := by
    apply hProj.mem_iff_map_id.mpr
    calc
      P (B x) = B (P x) := by
        exact (congrArg (fun f : Module.End ℚ V => f x) hComm).symm
      _ = B x := by rw [hProj.map_id x hx]
  let T : Module.End ℚ S := B.restrict hInvariant
  have hTSquare : T * T = a • (1 : Module.End ℚ S) := by
    ext x
    change B (B (x : V)) = a • (x : V)
    have h := congrArg (fun f : Module.End ℚ V => f (x : V)) hSquare
    change B (B (P (x : V))) = a • P (x : V) at h
    simpa only [hProj.map_id (x : V) x.property] using h
  exact rational_scalar_square_of_odd_finrank T a hTSquare hOdd

/-- A trace-zero rational involution in dimension two modulo four imposes a square-scalar obstruction. -/
theorem rational_involution_square_obstruction {n : ℕ}
    (B Z J : Matrix (Fin n) (Fin n) ℚ) (q : ℚ)
    (hInvolution : Z * Z = 1) (hTrace : Z.trace = 0)
    (hComm : B * Z = Z * B) (hSquare : B * B = q • (1 : Matrix (Fin n) (Fin n) ℚ) + J - Z)
    (hJZ : J * Z = J) (hDimension : n % 4 = 2) : IsSquare (q + 1) := by
  let P : Matrix (Fin n) (Fin n) ℚ := (1 / 2 : ℚ) • (1 - Z)
  have hIdem : P * P = P := by
    dsimp only [P]
    simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_one, one_mul, hInvolution]
    ext i j
    dsimp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hBP : B * P = P * B := by
    dsimp only [P]
    rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hComm]
  have hJP : J * P = 0 := by
    dsimp only [P]
    rw [mul_smul_comm, mul_sub, mul_one, hJZ, sub_self, smul_zero]
  have hZP : Z * P = -P := by
    dsimp only [P]
    rw [mul_smul_comm, mul_sub, mul_one, hInvolution]
    ext i j
    dsimp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hBP2 : B * B * P = (q + 1) • P := by
    rw [hSquare, sub_mul, add_mul, smul_mul_assoc, one_mul, hJP, hZP]
    ext i j
    dsimp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hTraceP : P.trace = (n : ℚ) / 2 := by
    dsimp only [P]
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, hTrace]
    simp
    ring
  let e : Matrix (Fin n) (Fin n) ℚ ≃ₐ[ℚ] Module.End ℚ (Fin n → ℚ) := Matrix.toLinAlgEquiv'
  let PL := e P
  let BL := e B
  have hIdemL : PL * PL = PL := by
    change e P * e P = e P
    rw [← map_mul, hIdem]
  have hCommL : BL * PL = PL * BL := by
    simpa only [map_mul] using congrArg e hBP
  have hSquareL : BL * BL * PL = (q + 1) • PL := by
    simpa only [map_mul, map_smul] using congrArg e hBP2
  have hTraceL : LinearMap.trace ℚ (Fin n → ℚ) PL = (n : ℚ) / 2 := by
    change LinearMap.trace ℚ (Fin n → ℚ) P.toLin' = _
    rw [Matrix.trace_toLin'_eq, hTraceP]
  let d := Module.finrank ℚ (LinearMap.range PL)
  have hRank : LinearMap.trace ℚ (Fin n → ℚ) PL = (d : ℚ) :=
    (LinearMap.IsIdempotentElem.isProj_range PL (show IsIdempotentElem PL from hIdemL)).trace
  have hTwice : 2 * d = n := by
    have hRational : 2 * (d : ℚ) = n := by linarith only [hRank, hTraceL]
    exact_mod_cast hRational
  have hOdd : Odd d := by
    refine ⟨d / 2, ?_⟩
    omega
  exact rational_scalar_square_on_projector BL PL (q + 1) hIdemL hCommL hSquareL hOdd

/-- A successor of a positive square lies strictly between consecutive squares. -/
theorem not_isSquare_sq_add_one (m : ℕ) (hm : 1 ≤ m) : ¬IsSquare (m ^ 2 + 1) := by
  rintro ⟨k, hk⟩
  by_cases hkm : k ≤ m
  · nlinarith
  · have hmk : m + 1 ≤ k := by omega
    nlinarith

/-- A unit-deficiency residual involution contradicts the square obstruction at square dyadic parameters. -/
theorem unit_deficiency_involution_impossible (q m : ℕ) (hm : 1 ≤ m)
    (hqSquare : q = m ^ 2) (hqMod : q % 4 = 0)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (hCases : ∀ v, signedDeficiency q G v = 0 ∨ signedDeficiency q G v = 1)
    (hInvolution : weightedResidual q G * weightedResidual q G = 1) : False := by
  let n := q ^ 2 + q + 2
  let f : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℚ := (Int.castRingHom ℚ).mapMatrix
  let B := f (weightedAdjacency q G)
  let Z := f (weightedResidual q G)
  let J := f (allOnesMatrix n)
  have hInv : Z * Z = 1 := by
    change f (weightedResidual q G) * f (weightedResidual q G) = 1
    rw [← map_mul, hInvolution, map_one]
  have hTrace : Z.trace = 0 := by
    change (∑ v, ((weightedResidual q G v v : ℤ) : ℚ)) = 0
    apply Finset.sum_eq_zero
    intro v _
    rw [weightedResidual_diagonal]
    rcases hCases v with h | h <;> simp [h]
  have hComm : B * Z = Z * B := by
    simpa only [map_mul] using congrArg f (weightedAdjacency_commutes_residual q G)
  have hDiagonal : Matrix.diagonal (fun _ : Fin n => (q : ℤ)) = (q : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hSquareInt : weightedAdjacency q G * weightedAdjacency q G =
      (q : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) + allOnesMatrix n - weightedResidual q G := by
    unfold weightedResidual
    rw [hDiagonal]
    abel
  have hScalar : f ((q : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) =
      (q : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    change (((q : ℤ) * (if i = j then (1 : ℤ) else 0) : ℤ) : ℚ) =
      (q : ℚ) * (if i = j then (1 : ℚ) else 0)
    by_cases hij : i = j <;> simp [hij]
  have hSquare : B * B = (q : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) + J - Z := by
    simpa only [map_mul, map_sub, map_add, hScalar] using congrArg f hSquareInt
  have hJZInt : allOnesMatrix n * weightedResidual q G = allOnesMatrix n := by
    ext v w
    rw [Matrix.mul_apply]
    change (∑ x, 1 * weightedResidual q G x w) = 1
    simp only [one_mul]
    calc
      _ = ∑ x, weightedResidual q G w x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (weightedResidual_symmetric q G).apply w x
      _ = 1 := weightedResidual_sum_row_one q G w
  have hJZ : J * Z = J := by
    simpa only [map_mul] using congrArg f hJZInt
  have hDim : n % 4 = 2 := by
    dsimp only [n]
    simp [Nat.add_mod, Nat.pow_mod, hqMod]
  have hRationalSquare := rational_involution_square_obstruction B Z J (q : ℚ) hInv hTrace hComm hSquare hJZ hDim
  have hNatSquare : IsSquare (q + 1) := Rat.isSquare_natCast_iff.mp (by
    simpa only [Nat.cast_add, Nat.cast_one] using hRationalSquare)
  rw [hqSquare] at hNatSquare
  exact not_isSquare_sq_add_one m hm hNatSquare

/-- The all-light alternative is impossible along the square dyadic subsequence. -/
theorem claimedBound_uniform_nonlight_exists (hBound : ClaimedBound) :
    ∃ T N : ℕ, ∀ k : ℕ, N ≤ 2 ^ (2 * (k + 1)) →
      ∀ G : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
        (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2) (cycleGraph 4) →
        (boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G).Nonempty := by
  obtain ⟨T, N, hAllLight⟩ := claimedBound_uniform_all_light_involution hBound
  refine ⟨T, N, ?_⟩
  intro k hk G hFree hEdges
  by_contra h
  have hEmpty := Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨hCases, hInv⟩ := hAllLight (2 * (k + 1)) hk G hFree hEdges hEmpty
  let q := 2 ^ (2 * (k + 1))
  let m := 2 ^ (k + 1)
  have hm : 1 ≤ m := by
    have hPositive : 0 < m := by dsimp [m]; positivity
    omega
  have hSquare : q = m ^ 2 := by
    dsimp only [q, m]
    rw [Nat.mul_comm 2 (k + 1), pow_mul]
  have hMod : q % 4 = 0 := by
    dsimp only [q]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    norm_num [Nat.mul_mod]
  exact unit_deficiency_involution_impossible q m hm hSquare hMod G hCases hInv

/-- The bounded light structure cannot exhaust the low vertices at a square parameter. -/
theorem nonlight_exists_of_bounded_light_structure (q m T R H J₀ : ℕ) (hm : 1 ≤ m)
    (hqSquare : q = m ^ 2) (hqMod : q % 4 = 0)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hIndependent : ∀ v ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj v w)
    (hLightRows : ∀ v ∈ boundedLightLowVertices q T G, (positivePartners q G v).card ≤ R)
    (hRegularRows : ∀ v, signedDeficiency q G v = 0 → (positivePartners q G v).card ≤ R)
    (hHigh : (highVertices q G).card ≤ H)
    (hJ : (boundedLightTriangleRegularVertices q T G).card ≤ J₀)
    (hHighOrder : J₀ + H + 4 < q) (hOrder : 3 * ((J₀ + J₀ ^ 2) * (R + 1)) < q) :
    (boundedNonlightLowVertices q T G).Nonempty := by
  by_contra h
  have hEmpty := Finset.not_nonempty_iff_eq_empty.mp h
  have hAll (v) (hv : v ∈ lowVertices q G) : v ∈ boundedLightLowVertices q T G := by
    by_contra hNot
    have hBad : v ∈ boundedNonlightLowVertices q T G := Finset.mem_sdiff.mpr ⟨hv, hNot⟩
    simp [hEmpty] at hBad
  have hNonnegative (v) : 0 ≤ signedDeficiency q G v := by
    by_contra hNegative
    have hvHigh := (mem_highVertices_iff q G v).mpr (show signedDeficiency q G v < 0 by omega)
    have hBound := all_lows_light_high_order_le q T G hFree hDegree hAll hIndependent v hvHigh
    omega
  have hCases := all_lows_light_deficiency_cases q T G hNonnegative hAll
  have hRows (v) : (positivePartners q G v).card ≤ R := by
    rcases hCases v with hZero | hOne
    · exact hRegularRows v hZero
    · exact hLightRows v (hAll v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
  have hOrderActual : 3 * (((boundedLightTriangleRegularVertices q T G).card +
      (boundedLightTriangleRegularVertices q T G).card ^ 2) * (R + 1)) < q := by
    apply lt_of_le_of_lt _ hOrder
    gcongr
  have hInvolution := all_lows_light_residual_square_eq_one q T R G hFree hNonnegative hAll hIndependent hRows hOrderActual
  exact unit_deficiency_involution_impossible q m hm hqSquare hqMod G hCases hInvolution


/-- The large maximum packing and its light-structure estimates can be chosen with the same threshold. -/
theorem claimedBound_uniform_structured_open_packing (hBound : ClaimedBound) :
    ∃ C K T M R Q E D N : ℕ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ D ∧ ∀ k : ℕ, N ≤ 2 ^ (2 * (k + 1)) →
      ∀ G : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2) (cycleGraph 4) →
        2 ^ (2 * (k + 1)) ≤ 4 * C * abovePlaneExcess (2 ^ (2 * (k + 1))) ^ 2 ∧
        (∀ v, G.degree v ≤ 2 ^ (2 * (k + 1)) + 2) ∧
        (highVertices (2 ^ (2 * (k + 1))) G).card ≤ 2611456 * C ∧
        (∑ v, positiveDeficiency (2 ^ (2 * (k + 1))) G v) ≤ 3 * (2 ^ (2 * (k + 1)) : ℕ) ∧
        (∀ v, signedDeficiency (2 ^ (2 * (k + 1))) G v ≤ K) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G,
          ∀ w ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G, ¬G.Adj l w) ∧
        (∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G).card ≤ M) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G,
          (triangularRegularNeighbors (2 ^ (2 * (k + 1))) G l).card ≤ 16 ∧
          (positivePartners (2 ^ (2 * (k + 1))) G l).card ≤ R) ∧
        (boundedLightTriangleRegularVertices (2 ^ (2 * (k + 1))) T G).card ≤ 72 ∧
        (∀ v, signedDeficiency (2 ^ (2 * (k + 1))) G v = 0 → (positivePartners (2 ^ (2 * (k + 1))) G v).card ≤ R) ∧
        (∀ v, 1 ≤ signedDeficiency (2 ^ (2 * (k + 1))) G v →
          ((positivePartners (2 ^ (2 * (k + 1))) G v).filter fun y => signedDeficiency (2 ^ (2 * (k + 1))) G y = 0 ∨
            y ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G).card ≤ Q) ∧
        ∃ P : Finset (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          P ⊆ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G ∧
          (zeroCodegreeGraph G).IsClique (P : Set _) ∧ 2 ^ (2 * (k + 1)) ≤ D * P.card ∧
          (∀ A ⊆ lowVertices (2 ^ (2 * (k + 1))) G, (zeroCodegreeGraph G).IsClique (A : Set _) → A.card ≤ P.card) ∧
          (∀ v ∈ lowVertices (2 ^ (2 * (k + 1))) G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) ∧
          ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  obtain ⟨_C, K, T, M, R, Q, _hC, hK, N₀, hStructure⟩ := claimedBound_uniform_light_structure hBound
  obtain ⟨C₀, hC₀, N₁, hPrep⟩ := claimedBound_uniform_preparation hBound
  obtain ⟨E, N₂, hCommon⟩ := claimedBound_uniform_common_zeroCodegree hBound
  let H := 2611456 * C₀
  let B := 2 * (T + 2)
  let D := 2 * B
  let cutoff := N₀ + N₁ + N₂ + 5222912 * C₀ + 48 * C₀ + H + 1 +
    2 * (T + 2) * (Q + 2 * H) + 6 * B ^ 2 * E +
    B * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) + D * (R + M + 2) +
    (H + 77) + (3 * ((72 + 72 ^ 2) * (R + 1)) + 1)
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hD : 1 ≤ D := by dsimp only [D]; omega
  refine ⟨C₀, K, T, M, R, Q, E, D, cutoff, hC₀, hK, hD, ?_⟩
  intro k hr G hFree hEdges
  let r := 2 * (k + 1)
  let q := 2 ^ r
  let S := boundedNonlightLowVertices q T G
  let L := lowVertices q G
  have hCutoff : cutoff ≤ q := hr
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₁ : N₁ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₂ : N₂ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have h48 : 48 * C₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHq : H ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hq : 0 < q := by dsimp only [cutoff] at hCutoff; omega
  have hRowsOrder : 2 * (T + 2) * (Q + 2 * H) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hGap : 6 * B ^ 2 * E ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hRamsey : B * 2 ^ ((6 * B * E + 1) + (18 * B ^ 2 + 1)) ≤ q := by
    dsimp only [cutoff] at hCutoff; omega
  have hLightOrder : D * (R + M + 2) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  obtain ⟨hGlobal, hIndependent, hNonlight, hLights, hJ, hRegular, hRows⟩ := hStructure r hN₀ G hFree hEdges
  obtain ⟨hExcess, hGraphs⟩ := hPrep r hN₁
  obtain ⟨_hNoCheap, _hMin, hDegree, hHigh, hPositive⟩ := hGraphs G hFree hEdges
  change q ≤ 4 * C₀ * abovePlaneExcess q ^ 2 at hExcess
  change (∀ v, G.degree v ≤ q + 2) at hDegree
  change (highVertices q G).card ≤ H at hHigh
  have hExcessThree : 3 ≤ abovePlaneExcess q := by
    by_contra h
    have hSmall : abovePlaneExcess q ≤ 2 := by omega
    have hSquare : abovePlaneExcess q ^ 2 ≤ 4 := by nlinarith only [hSmall]
    have hProduct := Nat.mul_le_mul_left (4 * C₀) hSquare
    omega
  have hDense := extremal_density_of_excess q G hEdges hExcessThree
  have hLowSize : L.card ≤ 3 * q := by
    exact_mod_cast dense_lowVertices_card_le q G hDegree hDense (hHigh.trans hHq)
  have hSL : S ⊆ L := Finset.sdiff_subset
  have hSize : S.card ≤ 3 * q := (Finset.card_le_card hSL).trans hLowSize
  have hCommonL (v) (hv : v ∈ L) (w) (hw : w ∈ L) (hNe : v ≠ w)
      (hNot : ¬(zeroCodegreeGraph G).Adj v w) : codegree (zeroCodegreeGraph G) v w ≤ E := by
    have hNZ : codegree G v w ≠ 0 := fun hz => hNot ⟨hNe, hz⟩
    have hOne : codegree G v w = 1 := by
      have hUpper := codegree_le_one G hFree v w hNe
      omega
    have hV : 1 ≤ signedDeficiency q G v := by have h := (Finset.mem_filter.mp hv).2; omega
    have hW : 1 ≤ signedDeficiency q G w := by have h := (Finset.mem_filter.mp hw).2; omega
    exact hCommon r hN₂ G hFree hEdges v w hNe hOne hV hW
  have hRowsActual : 2 * (T + 2) * (Q + 2 * (highVertices q G).card) ≤ q := by
    calc
      _ ≤ 2 * (T + 2) * (Q + 2 * H) := by gcongr
      _ ≤ _ := hRowsOrder
  have hHighOrder : 72 + H + 4 < q := by dsimp only [cutoff] at hCutoff; omega
  have hInvolutionOrder : 3 * ((72 + 72 ^ 2) * (R + 1)) < q := by dsimp only [cutoff] at hCutoff; omega
  let m := 2 ^ (k + 1)
  have hm : 1 ≤ m := by
    have hPositive : 0 < m := by dsimp [m]; positivity
    omega
  have hSquare : q = m ^ 2 := by
    dsimp only [q, r, m]
    rw [Nat.mul_comm 2 (k + 1), pow_mul]
  have hMod : q % 4 = 0 := by
    dsimp only [q, r]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    norm_num [Nat.mul_mod]
  have hNonempty := nonlight_exists_of_bounded_light_structure q m T R H 72 hm hSquare hMod G hFree
    hDegree hIndependent (fun v hv => (hLights v hv).2) hRegular hHigh hJ hHighOrder hInvolutionOrder
  have hPositiveBound : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ) := by
    have hOrder : 5222912 * C₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
    have hOrderInt : (5222912 : ℤ) * C₀ ≤ q := by exact_mod_cast hOrder
    change (∑ v, positiveDeficiency q G v) ≤ 2 * (q : ℤ) + 5222912 * C₀ at hPositive
    omega
  refine ⟨hExcess, hDegree, hHigh, hPositiveBound, hGlobal, hIndependent, hNonlight, hLights, hJ, hRegular, hRows, ?_⟩
  exact exists_open_packing_of_bounded_light q T B R M Q E rfl G hFree hDegree hIndependent hNonlight
    (fun v hv => (hLights v hv).2) hRows hLowSize hCommonL hRowsActual hGap hRamsey hLightOrder hNonempty

/-- The claimed bound forces a large maximum open packing along the square dyadic subsequence. -/
theorem claimedBound_uniform_open_packing (hBound : ClaimedBound) :
    ∃ T D E N : ℕ, 1 ≤ D ∧ ∀ k : ℕ, N ≤ 2 ^ (2 * (k + 1)) →
      ∀ G : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2) (cycleGraph 4) →
        ∃ P : Finset (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          P ⊆ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G ∧
          (zeroCodegreeGraph G).IsClique (P : Set _) ∧ 2 ^ (2 * (k + 1)) ≤ D * P.card ∧
          (∀ A ⊆ lowVertices (2 ^ (2 * (k + 1))) G, (zeroCodegreeGraph G).IsClique (A : Set _) → A.card ≤ P.card) ∧
          (∀ v ∈ lowVertices (2 ^ (2 * (k + 1))) G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) ∧
          ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  obtain ⟨_C, _K, T, _M, _R, _Q, E, D, N, _hC, _hK, hD, hData⟩ :=
    claimedBound_uniform_structured_open_packing hBound
  refine ⟨T, D, E, N, hD, ?_⟩
  intro k hk G hFree hEdges
  obtain ⟨_hExcess, _hDegree, _hHigh, _hPositive, _hGlobal, _hIndependent, _hNonlight,
    _hLights, _hJ, _hRegular, _hGood, hPacking⟩ := hData k hk G hFree hEdges
  exact hPacking



/-- Replace the neighborhood of v by the selected parent neighborhood. -/
def parentReplacement {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (T : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (if x = v then y ∈ T else if y = v then x ∈ T else G.Adj x y)
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    by_cases hx : x = v <;> by_cases hy : y = v <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem parentReplacement_root_adj {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) (x : Fin n) :
    (parentReplacement G v T).Adj v x ↔ x ≠ v ∧ x ∈ T := by
  simp [parentReplacement, ne_comm]

theorem parentReplacement_away_adj {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) (x y : Fin n) (hx : x ≠ v) (hy : y ≠ v) :
    (parentReplacement G v T).Adj x y ↔ G.Adj x y := by
  simp only [parentReplacement, ite_eq_right hx, ite_eq_right hy]
  exact ⟨And.right, fun h => ⟨h.ne, h⟩⟩

theorem parentReplacement_neighbor_root {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) : (parentReplacement G v T).neighborFinset v = T.erase v := by
  ext x
  rw [SimpleGraph.mem_neighborFinset, parentReplacement_root_adj]
  exact Finset.mem_erase.symm

theorem parentReplacement_neighbor_away {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) (x : Fin n) (hx : x ≠ v) :
    (parentReplacement G v T).neighborFinset x =
      (G.neighborFinset x).erase v ∪ if x ∈ T then {v} else ∅ := by
  ext y
  by_cases hy : y = v
  · subst y
    rw [SimpleGraph.mem_neighborFinset]
    change (x ≠ v ∧ (if x = v then v ∈ T else if v = v then x ∈ T else G.Adj x v)) ↔ _
    by_cases ht : x ∈ T <;> simp [hx, ht]
  · rw [SimpleGraph.mem_neighborFinset, parentReplacement_away_adj G v T x y hx hy]
    by_cases ht : x ∈ T <;> simp [ht, hy, SimpleGraph.mem_neighborFinset]

/-- A common neighbor of the new parent and another vertex is unique by the open-packing property. -/
theorem parentReplacement_root_common_unique {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n))
    (hOpen : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → codegree G x y = 0)
    (w x y : Fin n) (hw : w ≠ v)
    (hvx : (parentReplacement G v T).Adj v x) (hwx : (parentReplacement G v T).Adj w x)
    (hvy : (parentReplacement G v T).Adj v y) (hwy : (parentReplacement G v T).Adj w y) : x = y := by
  obtain ⟨hxv, hxT⟩ := (parentReplacement_root_adj G v T x).mp hvx
  obtain ⟨hyv, hyT⟩ := (parentReplacement_root_adj G v T y).mp hvy
  have hWX := (parentReplacement_away_adj G v T w x hw hxv).mp hwx
  have hWY := (parentReplacement_away_adj G v T w y hw hyv).mp hwy
  by_contra hxy
  exact (codegree_eq_zero_iff G x y).mp (hOpen x hxT y hyT hxy) w hWX.symm hWY.symm

theorem parentReplacement_free {n : ℕ} (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G)
    (v : Fin n) (T : Finset (Fin n))
    (hOpen : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → codegree G x y = 0) :
    (cycleGraph 4).Free (parentReplacement G v T) := by
  apply (free_iff_common_neighbor_unique (parentReplacement G v T)).mpr
  intro u w huw x y hux hwx huy hwy
  by_cases hu : u = v
  · subst u
    exact parentReplacement_root_common_unique G v T hOpen w x y huw.symm hux hwx huy hwy
  by_cases hw : w = v
  · subst w
    exact parentReplacement_root_common_unique G v T hOpen u x y hu hwx hux hwy huy
  by_cases hx : x = v
  · subst x
    by_cases hy : y = v
    · exact hy.symm
    have huT := ((parentReplacement_root_adj G v T u).mp hux.symm).2
    have hwT := ((parentReplacement_root_adj G v T w).mp hwx.symm).2
    have hUY := (parentReplacement_away_adj G v T u y hu hy).mp huy
    have hWY := (parentReplacement_away_adj G v T w y hw hy).mp hwy
    exact False.elim ((codegree_eq_zero_iff G u w).mp (hOpen u huT w hwT huw) y hUY hWY)
  by_cases hy : y = v
  · subst y
    have huT := ((parentReplacement_root_adj G v T u).mp huy.symm).2
    have hwT := ((parentReplacement_root_adj G v T w).mp hwy.symm).2
    have hUX := (parentReplacement_away_adj G v T u x hu hx).mp hux
    have hWX := (parentReplacement_away_adj G v T w x hw hx).mp hwx
    exact False.elim ((codegree_eq_zero_iff G u w).mp (hOpen u huT w hwT huw) x hUX hWX)
  exact common_neighbor_unique G hFree huw
    ((parentReplacement_away_adj G v T u x hu hx).mp hux)
    ((parentReplacement_away_adj G v T w x hw hx).mp hwx)
    ((parentReplacement_away_adj G v T u y hu hy).mp huy)
    ((parentReplacement_away_adj G v T w y hw hy).mp hwy)

theorem parentReplacement_degree_root {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) : (parentReplacement G v T).degree v = (T.erase v).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, parentReplacement_neighbor_root]

theorem parentReplacement_degree_balance {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) (x : Fin n) (hx : x ≠ v) :
    (parentReplacement G v T).degree x + (if G.Adj x v then 1 else 0) =
      G.degree x + (if x ∈ T then 1 else 0) := by
  have hCard : (parentReplacement G v T).degree x = ((G.neighborFinset x).erase v).card + (if x ∈ T then 1 else 0) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, parentReplacement_neighbor_away G v T x hx]
    by_cases ht : x ∈ T
    · rw [ite_eq_left ht, ite_eq_left ht, Finset.union_singleton, Finset.card_insert_of_notMem (Finset.notMem_erase _ _)]
    · simp only [ite_eq_right ht, Finset.union_empty, add_zero]
  have hErase : ((G.neighborFinset x).erase v).card + (if G.Adj x v then 1 else 0) = G.degree x := by
    by_cases hAdj : G.Adj x v
    · have h := Finset.card_erase_add_one ((G.mem_neighborFinset x v).mpr hAdj)
      simpa only [ite_eq_left hAdj, SimpleGraph.card_neighborFinset_eq_degree] using h
    · have hNot : v ∉ G.neighborFinset x := fun h => hAdj ((G.mem_neighborFinset x v).mp h)
      simp only [ite_eq_right hAdj, add_zero, Finset.erase_eq_of_notMem hNot, SimpleGraph.card_neighborFinset_eq_degree]
  omega

/-- The parent exchange deletes the old incident edges and inserts the selected ones. -/
theorem parentReplacement_edge_count {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) :
    (parentReplacement G v T).edgeFinset.card + G.degree v = G.edgeFinset.card + (T.erase v).card := by
  let U : Finset (Fin n) := Finset.univ.erase v
  have hSelected : (∑ x ∈ U, if x ∈ T then 1 else 0) = (T.erase v).card := by
    rw [← Finset.sum_filter]
    have hSet : U.filter (fun x => x ∈ T) = T.erase v := by ext x; simp [U, and_comm]
    simp [hSet]
  have hAdjacent : (∑ x ∈ U, if G.Adj x v then 1 else 0) = G.degree v := by
    rw [← Finset.sum_filter]
    have hSet : U.filter (fun x => G.Adj x v) = G.neighborFinset v := by
      ext x
      constructor
      · intro hx
        exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2.symm
      · intro hx
        have hAdj := (G.mem_neighborFinset v x).mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hAdj.ne.symm, Finset.mem_univ x⟩, hAdj.symm⟩
    simp [hSet]
  have hBalance : (∑ x ∈ U, (parentReplacement G v T).degree x) + G.degree v =
      (∑ x ∈ U, G.degree x) + (T.erase v).card := by
    have h := Finset.sum_congr rfl (fun x (hx : x ∈ U) => parentReplacement_degree_balance G v T x (Finset.mem_erase.mp hx).1)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hSelected, hAdjacent] at h
    exact h
  have hOld := Finset.sum_erase_add Finset.univ (fun x => G.degree x) (Finset.mem_univ v)
  have hNew := Finset.sum_erase_add Finset.univ (fun x => (parentReplacement G v T).degree x) (Finset.mem_univ v)
  rw [parentReplacement_degree_root] at hNew
  change (∑ x ∈ U, G.degree x) + G.degree v = _ at hOld
  change (∑ x ∈ U, (parentReplacement G v T).degree x) + (T.erase v).card = _ at hNew
  have hSumOld := G.sum_degrees_eq_twice_card_edges
  have hSumNew := (parentReplacement G v T).sum_degrees_eq_twice_card_edges
  omega

/-- Edge extremality bounds the size of any selected parent neighborhood by the old degree. -/
theorem extremal_parent_degree_bound {n : ℕ} (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G)
    (hEdges : G.edgeFinset.card = extremalNumber n (cycleGraph 4))
    (T : Finset (Fin n)) (hOpen : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → codegree G x y = 0) (v : Fin n) :
    (T.erase v).card ≤ G.degree v := by
  have hHFree := parentReplacement_free G hFree v T hOpen
  have hBound := SimpleGraph.card_edgeFinset_le_extremalNumber hHFree
  simp only [Fintype.card_fin] at hBound
  have hCount := parentReplacement_edge_count G v T
  omega


/-- Each graph neighborhood meets an open packing in at most one vertex. -/
theorem open_packing_neighbor_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (v : Fin n) :
    (G.neighborFinset v ∩ P).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hNe
  have hZero := hOpen x (Finset.mem_inter.mp hx).2 y (Finset.mem_inter.mp hy).2 hNe
  exact (codegree_eq_zero_iff G x y).mp hZero v
    ((G.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).1).symm
    ((G.mem_neighborFinset v y).mp (Finset.mem_inter.mp hy).1).symm

/-- A low open packing in an extremal graph has size at most q+1. -/
theorem extremal_low_open_packing_card_le_add_one (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hEdges : G.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4))
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) : P.card ≤ q + 1 := by
  by_cases hEmpty : P = ∅
  · simp [hEmpty]
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hParent := extremal_parent_degree_bound G hFree hEdges P hOpen v
  have hCard := Finset.card_erase_add_one hv
  have hPositive := (Finset.mem_filter.mp (hLow hv)).2
  unfold signedDeficiency at hPositive
  omega

/-- At size q+1 the parent exchanges force every packing vertex to be unit and every low into the packing. -/
theorem extremal_packing_at_add_one (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hEdges : G.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4))
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q + 1) :
    (∀ v ∈ P, signedDeficiency q G v = 1) ∧ lowVertices q G ⊆ P := by
  constructor
  · intro v hv
    have hParent := extremal_parent_degree_bound G hFree hEdges P hOpen v
    have hErase := Finset.card_erase_add_one hv
    have hPositive := (Finset.mem_filter.mp (hLow hv)).2
    unfold signedDeficiency at hPositive ⊢
    omega
  · intro v hv
    by_contra hNot
    have hParent := extremal_parent_degree_bound G hFree hEdges P hOpen v
    rw [Finset.erase_eq_of_notMem hNot, hCard] at hParent
    have hPositive := (Finset.mem_filter.mp hv).2
    unfold signedDeficiency at hPositive
    omega

/-- The exceptional size q+1 would leave no high vertices once q is at least three. -/
theorem extremal_packing_at_add_one_no_high (q : ℕ) (hq : 3 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hEdges : G.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4))
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q + 1) :
    ∀ v, 0 ≤ signedDeficiency q G v := by
  obtain ⟨hUnit, hAllLow⟩ := extremal_packing_at_add_one q G hFree hEdges P hLow hOpen hCard
  have hPositive (v) : positiveDeficiency q G v = if v ∈ P then 1 else 0 := by
    by_cases hv : v ∈ P
    · simp [positiveDeficiency, hUnit v hv, hv]
    · have hNotLow : ¬0 < signedDeficiency q G v := by
        intro h
        exact hv (hAllLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      rw [ite_eq_right hv]
      exact max_eq_right (show signedDeficiency q G v ≤ 0 by omega)
  intro v
  by_contra h
  have hHigh : q + 2 ≤ G.degree v := by unfold signedDeficiency at h; omega
  have hWeight := high_vertex_positive_neighbor_sum q G hFree v hHigh
  have hSum : (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) = (G.neighborFinset v ∩ P).card := by
    simp_rw [hPositive]
    simpa only [one_mul] using neighbor_indicator_weight_sum G v P (1 : ℤ)
  have hNeighbors : ((G.neighborFinset v ∩ P).card : ℤ) ≤ 1 := by
    exact_mod_cast open_packing_neighbor_card_le_one G P hOpen v
  rw [hSum] at hWeight
  omega

/-- Parity excludes q+1, so every low open packing has at most q vertices at an even parameter. -/
theorem extremal_low_open_packing_card_le (q : ℕ) (hq : 3 ≤ q) (hEven : Even q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hEdges : G.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4))
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) : P.card ≤ q := by
  have hUpper := extremal_low_open_packing_card_le_add_one q G hFree hEdges P hLow hOpen
  by_contra h
  have hCard : P.card = q + 1 := by omega
  obtain ⟨hUnit, hAllLow⟩ := extremal_packing_at_add_one q G hFree hEdges P hLow hOpen hCard
  have hNonnegative := extremal_packing_at_add_one_no_high q hq G hFree hEdges P hLow hOpen hCard
  have hSigned (v) : signedDeficiency q G v = if v ∈ P then 1 else 0 := by
    by_cases hv : v ∈ P
    · simpa only [ite_eq_left hv] using hUnit v hv
    · have hNotLow : ¬0 < signedDeficiency q G v := by
        intro h
        exact hv (hAllLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      have hNonneg := hNonnegative v
      rw [ite_eq_right hv]
      omega
  have hSum : (∑ v, signedDeficiency q G v) = (P.card : ℤ) := by
    simp_rw [hSigned]
    rw [← Finset.sum_filter]
    have hSet : (Finset.univ.filter fun v => v ∈ P) = P := by ext v; simp
    simp [hSet]
  have hHand := sum_signedDeficiency q G
  rw [hSum, hCard] at hHand
  obtain ⟨t, ht⟩ := hEven
  have hTwo : q = 2 * t := by omega
  push_cast at hHand
  have hTwoInt : (q : ℤ) = 2 * t := by exact_mod_cast hTwo
  rw [hTwoInt] at hHand
  have hMod := congrArg (fun z : ℤ => z % 2) hHand
  norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at hMod


/-- The vertices covered by at least one neighborhood of the selected packing. -/
def packingCovered {n : ℕ} (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => (G.neighborFinset v ∩ P).Nonempty

theorem open_packing_neighbor_indicator {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (v : Fin n) :
    ((G.neighborFinset v ∩ P).card : ℤ) = if v ∈ packingCovered G P then 1 else 0 := by
  have hUpper := open_packing_neighbor_card_le_one G P hOpen v
  by_cases hv : v ∈ packingCovered G P
  · have hPos := Finset.card_pos.mpr (Finset.mem_filter.mp hv).2
    rw [ite_eq_left hv]
    norm_cast
    omega
  · have hEmpty : ¬(G.neighborFinset v ∩ P).Nonempty := by
      intro h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hZero : (G.neighborFinset v ∩ P).card = 0 := by
      simpa only [Finset.card_eq_zero] using Finset.not_nonempty_iff_eq_empty.mp hEmpty
    simp only [ite_eq_right hv, hZero, Nat.cast_zero]

/-- An open packing counts each covered vertex exactly once. -/
theorem open_packing_covered_weight_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (a : Fin n → ℤ) :
    (∑ v ∈ packingCovered G P, a v) = ∑ t ∈ P, ∑ v ∈ G.neighborFinset t, a v := by
  rw [sum_selected_neighbor_weights]
  simp_rw [open_packing_neighbor_indicator G P hOpen]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hSet : (Finset.univ.filter fun v => v ∈ packingCovered G P) = packingCovered G P := by ext v; simp
  rw [hSet]

theorem open_packing_covered_card {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    ((packingCovered G P).card : ℤ) = ∑ t ∈ P, (G.degree t : ℤ) := by
  simpa using open_packing_covered_weight_sum G P hOpen (fun _ => 1)

/-- Count the selected neighbors using their adjacency indicators. -/
theorem neighbor_intersection_card_eq_sum_adjacency {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (v : Fin n) :
    ((G.neighborFinset v ∩ P).card : ℤ) = ∑ w ∈ P, if G.Adj v w then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hSet : P.filter (G.Adj v) = G.neighborFinset v ∩ P := by
    ext w
    simp [G.neighborFinset_eq_filter, and_comm]
  simp [hSet]

/-- Two-step incidences into a packing count neighbors in its covered set. -/
theorem open_packing_sum_codegree {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (v : Fin n) :
    (∑ t ∈ P, (codegree G v t : ℤ)) = ((G.neighborFinset v ∩ packingCovered G P).card : ℤ) := by
  have hCount := sum_neighbor_intersection_card G (G.neighborFinset v) P
  have hCountInt : (∑ t ∈ P, (codegree G v t : ℤ)) =
      ∑ w ∈ G.neighborFinset v, ((G.neighborFinset w ∩ P).card : ℤ) := by
    have h : (∑ t ∈ P, codegree G v t) = ∑ w ∈ G.neighborFinset v, (G.neighborFinset w ∩ P).card := by
      simpa only [codegree, Finset.inter_comm] using hCount.symm
    exact_mod_cast h
  rw [hCountInt]
  simp_rw [open_packing_neighbor_indicator G P hOpen]
  simpa only [one_mul] using neighbor_indicator_weight_sum G v (packingCovered G P) (1 : ℤ)

theorem open_packing_covered_neighbors_inside {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (v : Fin n) (hv : v ∈ P) :
    ((G.neighborFinset v ∩ packingCovered G P).card : ℤ) = G.degree v := by
  rw [← open_packing_sum_codegree G P hOpen]
  rw [Finset.sum_eq_single v]
  · simp [codegree]
  · intro t ht htv
    rw [hOpen v hv t ht htv.symm, Nat.cast_zero]
  · exact fun h => (h hv).elim

theorem open_packing_covered_neighbors_outside {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P : Finset (Fin n))
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (v : Fin n) (hv : v ∉ P) :
    ((G.neighborFinset v ∩ packingCovered G P).card : ℤ) +
      ((zeroCodegreeGraph G).neighborFinset v ∩ P).card = P.card := by
  rw [← open_packing_sum_codegree G P hOpen, neighbor_intersection_card_eq_sum_adjacency,
    ← Finset.sum_add_distrib]
  have hTerm (t) (ht : t ∈ P) :
      (codegree G v t : ℤ) + (if (zeroCodegreeGraph G).Adj v t then 1 else 0) = 1 := by
    have hNe : v ≠ t := fun h => hv (h ▸ ht)
    have hBound := codegree_le_one G hFree v t hNe
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hBound with h | h <;> simp [zeroCodegreeGraph, hNe, h]
  rw [Finset.sum_congr rfl hTerm]
  simp

/-- The zero-codegree neighbors inside a packing are all of its other vertices. -/
theorem open_packing_zero_neighbors_inside {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (v : Fin n) (hv : v ∈ P) :
    ((zeroCodegreeGraph G).neighborFinset v ∩ P).card + 1 = P.card := by
  have hSet : (zeroCodegreeGraph G).neighborFinset v ∩ P = P.erase v := by
    ext t
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
    constructor
    · intro h
      exact ⟨h.1.1.symm, h.2⟩
    · intro h
      exact ⟨⟨h.1.symm, hOpen v hv t h.2 h.1.symm⟩, h.2⟩
  rw [hSet]
  exact Finset.card_erase_add_one hv


/-- Pair coverage gives a quadratic identity for any selected vertex set. -/
theorem subset_neighbor_square_identity {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (U : Finset (Fin n)) :
    (∑ v, ((G.neighborFinset v ∩ U).card : ℤ) ^ 2) +
      (∑ v ∈ U, (((zeroCodegreeGraph G).neighborFinset v ∩ U).card : ℤ)) +
      (∑ v ∈ U, signedDeficiency q G v) = (U.card : ℤ) ^ 2 + q * U.card := by
  have hPair := pair_coverage_identity G hFree U
  rw [Finset.sum_sub_distrib] at hPair
  have hIncidence : (∑ v, ((G.neighborFinset v ∩ U).card : ℤ)) =
      ∑ v ∈ U, (G.degree v : ℤ) := by
    have h := sum_neighbor_intersection_card G Finset.univ U
    simp only [Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree] at h
    exact_mod_cast h
  have hDeficiency : (∑ v ∈ U, signedDeficiency q G v) =
      ((q : ℤ) + 1) * U.card - ∑ v ∈ U, (G.degree v : ℤ) := by
    simp [signedDeficiency, Finset.sum_sub_distrib, mul_comm]
  rw [hIncidence] at hPair
  nlinarith

/-- The outside zero-codegree incidence sum is fixed by the packing deficiencies. -/
theorem open_packing_outside_zero_sum (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2)))
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    (∑ v ∈ Finset.univ \ P, (((zeroCodegreeGraph G).neighborFinset v ∩ P).card : ℤ)) =
      ((q : ℤ) + 2 - P.card) * P.card + q * (∑ t ∈ P, (signedDeficiency q G t - 1)) +
        ∑ t ∈ P, ∑ v ∈ G.neighborFinset t, signedDeficiency q G v := by
  have hCount : (∑ v ∈ Finset.univ \ P, (((zeroCodegreeGraph G).neighborFinset v ∩ P).card : ℤ)) =
      ∑ t ∈ P, (((zeroCodegreeGraph G).neighborFinset t ∩ (Finset.univ \ P)).card : ℤ) := by
    exact_mod_cast sum_neighbor_intersection_card (zeroCodegreeGraph G) (Finset.univ \ P) P
  have hRow (t) (ht : t ∈ P) :
      (((zeroCodegreeGraph G).neighborFinset t ∩ (Finset.univ \ P)).card : ℤ) =
        (zeroCodegreeGraph G).degree t - P.card + 1 := by
    have hPartition := Finset.card_sdiff_add_card_inter ((zeroCodegreeGraph G).neighborFinset t) P
    have hInside := open_packing_zero_neighbors_inside G P hOpen t ht
    have hSet : (zeroCodegreeGraph G).neighborFinset t ∩ (Finset.univ \ P) =
        (zeroCodegreeGraph G).neighborFinset t \ P := by ext v; simp
    rw [hSet]
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hPartition
    omega
  rw [hCount]
  calc
    _ = ∑ t ∈ P, ((zeroCodegreeGraph G).degree t - (P.card : ℤ) + 1) := Finset.sum_congr rfl hRow
    _ = _ := by
      simp_rw [zeroCodegree_degree_identity q G hFree]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum, mul_one]
      ring

/-- The summed packing Gram identity, retaining every signed term. -/
theorem open_packing_gram_sum_identity (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2)))
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    ((q : ℤ) + 2 - P.card) * (P.card : ℤ) ^ 2 +
      (∑ t ∈ P, (signedDeficiency q G t - 1)) ^ 2 +
      (2 * (P.card : ℤ) - 1) * (∑ t ∈ P, ∑ v ∈ G.neighborFinset t, signedDeficiency q G v) =
      (∑ v ∈ Finset.univ \ P, (((zeroCodegreeGraph G).neighborFinset v ∩ P).card : ℤ) ^ 2) +
      (∑ v ∈ packingCovered G P, (((zeroCodegreeGraph G).neighborFinset v ∩ packingCovered G P).card : ℤ)) +
      (∑ t ∈ P, (signedDeficiency q G t - 1) ^ 2) - q * (∑ t ∈ P, (signedDeficiency q G t - 1)) := by
  let U := packingCovered G P
  let E : Finset (Fin (q ^ 2 + q + 2)) := Finset.univ \ P
  let p : ℤ := P.card
  let τ : ℤ := ∑ t ∈ P, (signedDeficiency q G t - 1)
  let b : ℤ := ∑ t ∈ P, ∑ v ∈ G.neighborFinset t, signedDeficiency q G v
  let z : Fin (q ^ 2 + q + 2) → ℤ := fun v => ((zeroCodegreeGraph G).neighborFinset v ∩ P).card
  have hDegree (t) : (G.degree t : ℤ) = (q : ℤ) - (signedDeficiency q G t - 1) := by
    unfold signedDeficiency
    ring
  have hCovered : (U.card : ℤ) = q * p - τ := by
    rw [open_packing_covered_card G P hOpen]
    simp_rw [hDegree]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    dsimp only [p, τ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have hOutsideCard : (E.card : ℤ) + p = (q : ℤ) ^ 2 + q + 2 := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (q ^ 2 + q + 2))) P
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
    dsimp only [E, p]
    exact_mod_cast h
  have hInsideSquares : (∑ t ∈ P, (G.degree t : ℤ) ^ 2) =
      p * (q : ℤ) ^ 2 - 2 * q * τ + ∑ t ∈ P, (signedDeficiency q G t - 1) ^ 2 := by
    simp_rw [hDegree, sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    dsimp only [p, τ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hOutsideSquares : (∑ v ∈ E, (p - z v) ^ 2) =
      E.card * p ^ 2 - 2 * p * (∑ v ∈ E, z v) + ∑ v ∈ E, z v ^ 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
  have hSquareSplit : (∑ v, ((G.neighborFinset v ∩ U).card : ℤ) ^ 2) =
      (∑ t ∈ P, (G.degree t : ℤ) ^ 2) + ∑ v ∈ E, (p - z v) ^ 2 := by
    have h := Finset.sum_sdiff (f := fun v => ((G.neighborFinset v ∩ U).card : ℤ) ^ 2) (Finset.subset_univ P)
    have hInside : (∑ t ∈ P, ((G.neighborFinset t ∩ U).card : ℤ) ^ 2) = ∑ t ∈ P, (G.degree t : ℤ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [open_packing_covered_neighbors_inside G P hOpen t ht]
    have hOutside : (∑ v ∈ E, ((G.neighborFinset v ∩ U).card : ℤ) ^ 2) = ∑ v ∈ E, (p - z v) ^ 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      have hNot : v ∉ P := (Finset.mem_sdiff.mp hv).2
      have hRow := open_packing_covered_neighbors_outside G hFree P hOpen v hNot
      have hEntry : ((G.neighborFinset v ∩ U).card : ℤ) = p - z v := by
        dsimp only [p, z, U]
        linarith
      rw [hEntry]
    change (∑ v ∈ E, ((G.neighborFinset v ∩ U).card : ℤ) ^ 2) +
      (∑ v ∈ P, ((G.neighborFinset v ∩ U).card : ℤ) ^ 2) = _ at h
    rw [hInside, hOutside] at h
    omega
  have hWeight : (∑ v ∈ U, signedDeficiency q G v) = b :=
    open_packing_covered_weight_sum G P hOpen (signedDeficiency q G)
  have hOutsideSum : (∑ v ∈ E, z v) = ((q : ℤ) + 2 - p) * p + q * τ + b :=
    open_packing_outside_zero_sum q G hFree P hOpen
  have hCoverage := subset_neighbor_square_identity q G hFree U
  rw [hSquareSplit, hInsideSquares, hOutsideSquares, hWeight, hCovered, hOutsideSum] at hCoverage
  change ((q : ℤ) + 2 - p) * p ^ 2 + τ ^ 2 + (2 * p - 1) * b =
    (∑ v ∈ E, z v ^ 2) + (∑ v ∈ U, (((zeroCodegreeGraph G).neighborFinset v ∩ U).card : ℤ)) +
      (∑ t ∈ P, (signedDeficiency q G t - 1) ^ 2) - q * τ
  nlinarith [hCoverage, congrArg (fun t : ℤ => t * p ^ 2) hOutsideCard]


/-- The weighted low-neighbor second moment follows from the adjacency energy identity. -/
theorem positive_neighbor_square_sum_le (q K : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ)) :
    (∑ v, (∑ w ∈ G.neighborFinset v, positiveDeficiency q G w) ^ 2) ≤
      (3 * (K : ℤ) + 9) * q ^ 2 := by
  let x := positiveDeficiency q G
  have hx (v) : 0 ≤ x v := positiveDeficiency_nonnegative q G v
  have hxK (v) : x v ≤ K := max_le (hGlobal v) (Int.natCast_nonneg K)
  have hDiagonal (v) : ((G.degree v : ℤ) - 1) * x v ^ 2 ≤ (q : ℤ) * x v ^ 2 := by
    by_cases hZero : x v = 0
    · simp [hZero]
    · have hLow : 0 < signedDeficiency q G v := by
        by_contra h
        have hNonpos : signedDeficiency q G v ≤ 0 := by omega
        exact hZero (max_eq_right hNonpos)
      have hDegree : (G.degree v : ℤ) - 1 ≤ q := by unfold signedDeficiency at hLow; omega
      exact mul_le_mul_of_nonneg_right hDegree (sq_nonneg _)
  have hDiagonalSum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hDiagonal v)
  rw [← Finset.mul_sum] at hDiagonalSum
  have hCorrection : 0 ≤ x ⬝ᵥ ((zeroCodegreeGraph G).adjMatrix ℤ *ᵥ x) := by
    unfold dotProduct
    apply Finset.sum_nonneg
    intro v _
    apply mul_nonneg (hx v)
    rw [(zeroCodegreeGraph G).adjMatrix_mulVec_apply]
    exact Finset.sum_nonneg (fun w _ => hx w)
  have hEnergy := adjMatrix_defect_energy q G hFree x
  have hSquares : (∑ v, x v ^ 2) ≤ (K : ℤ) * (∑ v, x v) := by
    calc
      _ ≤ ∑ v, (K : ℤ) * x v := by
        apply Finset.sum_le_sum
        intro v _
        nlinarith [hx v, hxK v]
      _ = _ := by rw [Finset.mul_sum]
  have hSumNonnegative : 0 ≤ ∑ v, x v := Finset.sum_nonneg (fun v _ => hx v)
  have hTotal' : (∑ v, x v) ≤ 3 * (q : ℤ) := hTotal
  have hSquareBound : (∑ v, x v) ^ 2 ≤ 9 * (q : ℤ) ^ 2 := by nlinarith
  have hScaled := mul_le_mul_of_nonneg_left hSquares (Int.natCast_nonneg q)
  have hScaledTotal := mul_le_mul_of_nonneg_left hTotal' (show 0 ≤ (q : ℤ) * K by positivity)
  have hOutput : (∑ v, (∑ w ∈ G.neighborFinset v, x w) ^ 2) = vectorSquareSum (G.adjMatrix ℤ *ᵥ x) := by
    simp only [vectorSquareSum, G.adjMatrix_mulVec_apply]
  rw [hOutput]
  nlinarith [hEnergy]

/-- Bounded outside low columns and bounded deficiencies control every outside packing column in square sum. -/
theorem open_packing_outside_zero_square_le (q K E H : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ))
    (hHigh : (highVertices q G).card ≤ H)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hCard : P.card ≤ q)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) :
    (∑ v ∈ Finset.univ \ P, (((zeroCodegreeGraph G).neighborFinset v ∩ P).card : ℤ) ^ 2) ≤
      (3 * (E : ℤ) ^ 2 + H + 6 * K + 22) * q ^ 2 := by
  let z : Fin (q ^ 2 + q + 2) → ℤ := fun v => ((zeroCodegreeGraph G).neighborFinset v ∩ P).card
  let c : Fin (q ^ 2 + q + 2) → ℤ := fun v => ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w
  let b : Fin (q ^ 2 + q + 2) → ℤ := fun v =>
    (if v ∈ lowVertices q G then (E : ℤ) ^ 2 else 0) +
    (if v ∈ highVertices q G then (q : ℤ) ^ 2 else 0) + 2 + 2 * c v ^ 2
  have hb (v) : 0 ≤ b v := by
    dsimp only [b]
    positivity
  have hz (v) : 0 ≤ z v := Int.natCast_nonneg _
  have hBound (v) (hv : v ∈ Finset.univ \ P) : z v ^ 2 ≤ b v := by
    have hNot : v ∉ P := (Finset.mem_sdiff.mp hv).2
    by_cases hLow : v ∈ lowVertices q G
    · have hZ : z v ≤ E := by
        dsimp only [z]
        exact_mod_cast hOutside v hLow hNot
      have hSquare : z v ^ 2 ≤ (E : ℤ) ^ 2 := by nlinarith [hz v]
      dsimp only [b]
      rw [ite_eq_left hLow]
      have hHighTerm : 0 ≤ if v ∈ highVertices q G then (q : ℤ) ^ 2 else 0 := by positivity
      nlinarith [sq_nonneg (c v)]
    · by_cases hHighV : v ∈ highVertices q G
      · have hZ : z v ≤ q := by
          dsimp only [z]
          have hInter := Finset.card_le_card (Finset.inter_subset_right : (zeroCodegreeGraph G).neighborFinset v ∩ P ⊆ P)
          exact_mod_cast hInter.trans hCard
        dsimp only [b]
        rw [ite_eq_right hLow, ite_eq_left hHighV]
        nlinarith [hz v, sq_nonneg (c v)]
      · have hRegular : signedDeficiency q G v = 0 := by
          have hLow' : ¬0 < signedDeficiency q G v := by
            intro h
            exact hLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hHigh' : ¬signedDeficiency q G v < 0 := by
            intro h
            exact hHighV ((mem_highVertices_iff q G v).mpr h)
          omega
        have hZ : z v ≤ 1 + c v := by
          have hInter : z v ≤ (zeroCodegreeGraph G).degree v := by
            dsimp only [z]
            exact_mod_cast (show ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ (zeroCodegreeGraph G).degree v by
              simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card
                (Finset.inter_subset_left : (zeroCodegreeGraph G).neighborFinset v ∩ P ⊆ (zeroCodegreeGraph G).neighborFinset v))
          have hRow := zeroCodegree_degree_identity q G hFree v
          rw [hRegular, mul_zero, add_zero] at hRow
          have hWeights : (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) ≤ c v :=
            Finset.sum_le_sum (fun w _ => le_max_left _ _)
          linarith
        have hc : 0 ≤ c v := Finset.sum_nonneg (fun w _ => positiveDeficiency_nonnegative q G w)
        dsimp only [b]
        rw [ite_eq_right hLow, ite_eq_right hHighV]
        nlinarith [hz v, sq_nonneg (c v - 1)]
  have hSum : (∑ v ∈ Finset.univ \ P, z v ^ 2) ≤ ∑ v, b v := by
    exact (Finset.sum_le_sum hBound).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hb v))
  have hLowSum : (∑ v, if v ∈ lowVertices q G then (E : ℤ) ^ 2 else 0) = (lowVertices q G).card * (E : ℤ) ^ 2 := by
    rw [← Finset.sum_filter]
    simp
  have hHighSum : (∑ v, if v ∈ highVertices q G then (q : ℤ) ^ 2 else 0) = (highVertices q G).card * (q : ℤ) ^ 2 := by
    rw [← Finset.sum_filter]
    simp
  have hSumB : (∑ v, b v) = (lowVertices q G).card * (E : ℤ) ^ 2 +
      (highVertices q G).card * (q : ℤ) ^ 2 + 2 * (q ^ 2 + q + 2 : ℕ) + 2 * (∑ v, c v ^ 2) := by
    dsimp only [b]
    simp only [Finset.sum_add_distrib, hLowSum, hHighSum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hLowCard : ((lowVertices q G).card : ℤ) ≤ 3 * q := (lowVertices_card_le_positiveDeficiency q G).trans hTotal
  have hHighCard : ((highVertices q G).card : ℤ) ≤ H := by exact_mod_cast hHigh
  have hMoment : (∑ v, c v ^ 2) ≤ (3 * (K : ℤ) + 9) * q ^ 2 :=
    positive_neighbor_square_sum_le q K G hFree hGlobal hTotal
  have hqInt : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hqSquare : (q : ℤ) ≤ q ^ 2 := by nlinarith
  have hOrder : ((q ^ 2 + q + 2 : ℕ) : ℤ) ≤ 2 * (q : ℤ) ^ 2 := by push_cast; nlinarith
  have hLowScaled := mul_le_mul_of_nonneg_right hLowCard (sq_nonneg (E : ℤ))
  have hLowScaled' := mul_le_mul_of_nonneg_left hqSquare (show 0 ≤ 3 * (E : ℤ) ^ 2 by positivity)
  have hHighScaled := mul_le_mul_of_nonneg_right hHighCard (sq_nonneg (q : ℤ))
  change (∑ v ∈ Finset.univ \ P, z v ^ 2) ≤ _
  rw [hSumB] at hSum
  nlinarith [hSum, hMoment]

/-- The summed Gram identity bounds the packing deficit using a bound for its outside columns. -/
theorem open_packing_gram_deficit_bound (q R H : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hHigh : (highVertices q G).card ≤ H)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hNonempty : P.Nonempty) (hCard : P.card ≤ q)
    (hSquares : (∑ v ∈ Finset.univ \ P, (((zeroCodegreeGraph G).neighborFinset v ∩ P).card : ℤ) ^ 2) ≤ (R : ℤ) * q ^ 2) :
    ((q : ℤ) + 2 - P.card) * (P.card : ℤ) ^ 2 ≤ (R + 6 + 2 * (H : ℤ)) * q ^ 2 := by
  let U := packingCovered G P
  let b : ℤ := ∑ t ∈ P, ∑ v ∈ G.neighborFinset t, signedDeficiency q G v
  have hGram := open_packing_gram_sum_identity q G hFree P hOpen
  have hLower : -(H : ℤ) ≤ b := by
    have hEq := sum_positiveDeficiency_eq_signed_add_high q G hDegree U
    have hNonnegative : 0 ≤ ∑ v ∈ U, positiveDeficiency q G v :=
      Finset.sum_nonneg (fun v _ => positiveDeficiency_nonnegative q G v)
    have hCount : ((U ∩ highVertices q G).card : ℤ) ≤ H := by
      exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right : U ∩ highVertices q G ⊆ highVertices q G)).trans hHigh
    rw [open_packing_covered_weight_sum G P hOpen (signedDeficiency q G)] at hEq
    change _ = b + _ at hEq
    omega
  have hCorrection : (∑ t ∈ P, (signedDeficiency q G t - 1) ^ 2) ≤
      (q : ℤ) * ∑ t ∈ P, (signedDeficiency q G t - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have hPositive := (Finset.mem_filter.mp (hLow ht)).2
    have hUpper : signedDeficiency q G t - 1 ≤ q := by unfold signedDeficiency; omega
    nlinarith
  have hZeros : (∑ v ∈ U, (((zeroCodegreeGraph G).neighborFinset v ∩ U).card : ℤ)) ≤ 6 * (q : ℤ) ^ 2 := by
    calc
      _ ≤ ∑ v ∈ U, ((zeroCodegreeGraph G).degree v : ℤ) := by
        apply Finset.sum_le_sum
        intro v _
        exact_mod_cast (show ((zeroCodegreeGraph G).neighborFinset v ∩ U).card ≤ (zeroCodegreeGraph G).degree v by
          simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card
            (Finset.inter_subset_left : (zeroCodegreeGraph G).neighborFinset v ∩ U ⊆ (zeroCodegreeGraph G).neighborFinset v))
      _ ≤ ∑ v, ((zeroCodegreeGraph G).degree v : ℤ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun _ _ _ => Int.natCast_nonneg _)
      _ ≤ _ := dense_zeroCodegree_count_le q hq G hFree hDense
  have hpNat : 1 ≤ P.card := Finset.card_pos.mpr hNonempty
  have hp : (1 : ℤ) ≤ P.card := by exact_mod_cast hpNat
  have hpq : (P.card : ℤ) ≤ q := by exact_mod_cast hCard
  have hScaled := mul_le_mul_of_nonneg_left hLower (show 0 ≤ 2 * (P.card : ℤ) - 1 by omega)
  have hqInt : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hqSquare : (q : ℤ) ≤ q ^ 2 := by nlinarith
  have hCardScaled := mul_le_mul_of_nonneg_right hpq (show 0 ≤ 2 * (H : ℤ) by positivity)
  have hQuadScaled := mul_le_mul_of_nonneg_left hqSquare (show 0 ≤ 2 * (H : ℤ) by positivity)
  have hTau := sq_nonneg (∑ t ∈ P, (signedDeficiency q G t - 1))
  change _ + _ + (2 * (P.card : ℤ) - 1) * b = _ at hGram
  change _ ≤ 6 * (q : ℤ) ^ 2 at hZeros
  nlinarith [hGram, hSquares, hCorrection, hZeros, hScaled, hCardScaled, hQuadScaled, hTau]


/-- A linear-size open packing has a bounded additive deficit under the prepared estimates. -/
theorem open_packing_card_gap_le (q K E H D : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDense : q * (q + 1) ^ 2 + 6 ≤ 2 * G.edgeFinset.card)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ))
    (hHigh : (highVertices q G).card ≤ H)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hCard : P.card ≤ q) (hLarge : q ≤ D * P.card)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) :
    q + 2 ≤ P.card + (3 * E ^ 2 + H + 6 * K + 22 + 6 + 2 * H) * D ^ 2 := by
  let R := 3 * E ^ 2 + H + 6 * K + 22
  have hSquares : (∑ v ∈ Finset.univ \ P, (((zeroCodegreeGraph G).neighborFinset v ∩ P).card : ℤ) ^ 2) ≤ (R : ℤ) * q ^ 2 := by
    simpa only [R, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      open_packing_outside_zero_square_le q K E H hq G hFree hGlobal hTotal hHigh P hCard hOutside
  have hNonempty : P.Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have hZero : P.card = 0 := by omega
    rw [hZero, mul_zero] at hLarge
    omega
  have hGram := open_packing_gram_deficit_bound q R H hq G hFree hDense hDegree hHigh P hLow hOpen hNonempty hCard hSquares
  have hLargeInt : (q : ℤ) ≤ (D : ℤ) * P.card := by exact_mod_cast hLarge
  have hSizeSq : (q : ℤ) ^ 2 ≤ (D : ℤ) ^ 2 * (P.card : ℤ) ^ 2 := by
    have h := (sq_le_sq₀ (Int.natCast_nonneg q) (show 0 ≤ (D : ℤ) * P.card by positivity)).mpr hLargeInt
    simpa only [mul_pow] using h
  have hp : (0 : ℤ) < P.card := by exact_mod_cast Finset.card_pos.mpr hNonempty
  have hpSq : (0 : ℤ) < (P.card : ℤ) ^ 2 := sq_pos_of_pos hp
  have hCoefficient : 0 ≤ (R : ℤ) + 6 + 2 * H := by positivity
  have hResult : (q : ℤ) + 2 - P.card ≤ ((R : ℤ) + 6 + 2 * H) * D ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hpSq).mp
    calc
      _ ≤ ((R : ℤ) + 6 + 2 * H) * q ^ 2 := hGram
      _ ≤ ((R : ℤ) + 6 + 2 * H) * ((D : ℤ) ^ 2 * (P.card : ℤ) ^ 2) :=
        mul_le_mul_of_nonneg_left hSizeSq hCoefficient
      _ = _ := by ring
  have hNat : q + 2 ≤ P.card + (R + 6 + 2 * H) * D ^ 2 := by
    exact_mod_cast (show (q : ℤ) + 2 ≤ P.card + ((R : ℤ) + 6 + 2 * H) * D ^ 2 by linarith)
  exact hNat

/-- Under the claimed bound, maximum low open packings differ from q by a fixed constant. -/
theorem claimedBound_uniform_almost_full_packing (hBound : ClaimedBound) :
    ∃ T D E J N : ℕ, 1 ≤ D ∧ ∀ k : ℕ, N ≤ 2 ^ (2 * (k + 1)) →
      ∀ G : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2) (cycleGraph 4) →
        ∃ P : Finset (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          P ⊆ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G ∧
          (zeroCodegreeGraph G).IsClique (P : Set _) ∧
          2 ^ (2 * (k + 1)) ≤ D * P.card ∧ P.card ≤ 2 ^ (2 * (k + 1)) ∧
          2 ^ (2 * (k + 1)) + 2 ≤ P.card + J ∧
          (∀ A ⊆ lowVertices (2 ^ (2 * (k + 1))) G, (zeroCodegreeGraph G).IsClique (A : Set _) → A.card ≤ P.card) ∧
          (∀ v ∈ lowVertices (2 ^ (2 * (k + 1))) G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) ∧
          ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  obtain ⟨T, D, E, N₀, hD, hPacking⟩ := claimedBound_uniform_open_packing hBound
  obtain ⟨C, hC, N₁, hPrep⟩ := claimedBound_uniform_preparation hBound
  obtain ⟨K, _hK, N₂, hGlobal⟩ := claimedBound_uniform_bounded_deficiency hBound
  let H := 2611456 * C
  let J := (3 * E ^ 2 + H + 6 * K + 22 + 6 + 2 * H) * D ^ 2
  let cutoff := N₀ + N₁ + N₂ + 5222912 * C + 48 * C + 3
  refine ⟨T, D, E, J, cutoff, hD, ?_⟩
  intro k hk G hFree hEdges
  let r := 2 * (k + 1)
  let q := 2 ^ r
  have hCutoff : cutoff ≤ q := hk
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₁ : N₁ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hN₂ : N₂ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hWeightOrder : 5222912 * C ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hExcessOrder : 16 * C < q := by dsimp only [cutoff] at hCutoff; omega
  have hq : 3 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  obtain ⟨P, hPN, hClique, hLarge, hMaximum, hOutside, hDisjoint⟩ := hPacking k hN₀ G hFree hEdges
  have hLow : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hPN hv)).1
  have hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0 := by
    intro v hv w hw hNe
    exact (hClique hv hw hNe).2
  have hEven : Even q := by
    refine ⟨2 ^ (2 * k + 1), ?_⟩
    dsimp only [q, r]
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    omega
  have hCard := extremal_low_open_packing_card_le q hq hEven G hFree hEdges P hLow hOpen
  obtain ⟨hExcess, hGraphs⟩ := hPrep r hN₁
  obtain ⟨_hNoCheap, _hMin, hDegree, hHigh, hPositive⟩ := hGraphs G hFree hEdges
  have hExcessThree : 3 ≤ abovePlaneExcess q := by
    by_contra h
    have hSmall : abovePlaneExcess q ≤ 2 := by omega
    have hSquare : abovePlaneExcess q ^ 2 ≤ 4 := by nlinarith only [hSmall]
    have hProduct := Nat.mul_le_mul_left (4 * C) hSquare
    change q ≤ 4 * C * abovePlaneExcess q ^ 2 at hExcess
    omega
  have hDense := extremal_density_of_excess q G hEdges hExcessThree
  have hTotal : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ) := by
    have hWeightInt : (5222912 : ℤ) * C ≤ q := by exact_mod_cast hWeightOrder
    change (∑ v, positiveDeficiency q G v) ≤ 2 * (q : ℤ) + 5222912 * C at hPositive
    omega
  have hGap := open_packing_card_gap_le q K E H D (by omega) G hFree hDense hDegree
    (hGlobal r hN₂ G hFree hEdges) hTotal hHigh P hLow hOpen hCard hLarge hOutside
  exact ⟨P, hPN, hClique, hLarge, hCard, hGap, hMaximum, hOutside, hDisjoint⟩


/-- Nonlow vertices outside all neighborhoods of the packing. -/
def packingHoles {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ packingCovered G P) \ lowVertices q G

/-- The unit-deficiency rows of a packing. -/
def packingUnitRows {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  P.filter fun t => signedDeficiency q G t = 1

/-- Total positive deficiency is the signed weight on the low vertices. -/
theorem lowVertices_signed_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) :
    (∑ v ∈ lowVertices q G, signedDeficiency q G v) = ∑ v, positiveDeficiency q G v := by
  rw [lowVertices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : 0 < signedDeficiency q G v
  · rw [ite_eq_left h]
    exact (max_eq_left (le_of_lt h)).symm
  · rw [ite_eq_right h]
    exact (max_eq_right (by omega)).symm

/-- The edge excess determines the total signed deficiency exactly. -/
theorem signedDeficiency_sum_of_excess (q a : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hEdges : G.edgeFinset.card = planeEdgeCount q + a) :
    (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a := by
  have hSum := sum_signedDeficiency q G
  rw [edgeSet_ncard, hEdges] at hSum
  have hTwice : 2 * (planeEdgeCount q : ℤ) = (q : ℤ) * (q + 1) ^ 2 := by
    exact_mod_cast twice_planeEdgeCount q
  push_cast at hSum
  nlinarith [hTwice]

/-- The packing excess is nonnegative because every selected vertex is low. -/
theorem packing_excess_nonnegative {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hLow : P ⊆ lowVertices q G) :
    0 ≤ ∑ t ∈ P, (signedDeficiency q G t - 1) := by
  apply Finset.sum_nonneg
  intro t ht
  have hPositive := (Finset.mem_filter.mp (hLow ht)).2
  omega

/-- Each nonunit low row uses at least one unit of the packing's excess. -/
theorem packing_unit_rows_lower {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hLow : P ⊆ lowVertices q G) :
    (P.card : ℤ) ≤ (packingUnitRows q G P).card + ∑ t ∈ P, (signedDeficiency q G t - 1) := by
  have hPointwise (t) (ht : t ∈ P) :
      (1 : ℤ) ≤ (if signedDeficiency q G t = 1 then 1 else 0) + (signedDeficiency q G t - 1) := by
    have hPositive := (Finset.mem_filter.mp (hLow ht)).2
    by_cases h : signedDeficiency q G t = 1
    · simp [h]
    · simp only [ite_eq_right h, zero_add]
      omega
  have hSum := Finset.sum_le_sum hPointwise
  have hUnits : (∑ t ∈ P, if signedDeficiency q G t = 1 then (1 : ℤ) else 0) = (packingUnitRows q G P).card := by
    rw [← Finset.sum_filter]
    simp [packingUnitRows]
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib, hUnits] using hSum

/-- The low-set cardinality plus packing excess is at most the total positive weight. -/
theorem low_card_add_packing_excess_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hLow : P ⊆ lowVertices q G) :
    (lowVertices q G).card + (∑ t ∈ P, (signedDeficiency q G t - 1)) ≤ ∑ v, positiveDeficiency q G v := by
  have hSplit := Finset.sum_sdiff (f := signedDeficiency q G) hLow
  have hOutside : ((lowVertices q G \ P).card : ℤ) ≤ ∑ v ∈ lowVertices q G \ P, signedDeficiency q G v := by
    calc
      _ = ∑ _v ∈ lowVertices q G \ P, (1 : ℤ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        have hPositive := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
        omega
  have hInside : (∑ t ∈ P, (signedDeficiency q G t - 1)) = (∑ t ∈ P, signedDeficiency q G t) - P.card := by
    simp [Finset.sum_sub_distrib]
  have hCard : ((lowVertices q G \ P).card : ℤ) + P.card = (lowVertices q G).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hLow
  rw [lowVertices_signed_sum] at hSplit
  linarith

/-- Count holes by subtracting the covered nonlow vertices. -/
theorem packing_holes_card_identity (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (P : Finset (Fin (q ^ 2 + q + 2)))
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    ((packingHoles q G P).card : ℤ) = ((q : ℤ) + 1 - P.card) * q + 2 - (lowVertices q G).card +
      (∑ t ∈ P, (signedDeficiency q G t - 1)) + (packingCovered G P ∩ lowVertices q G).card := by
  let U := packingCovered G P
  let S := lowVertices q G
  have hA := Finset.card_sdiff_add_card_inter (Finset.univ \ U) S
  have hB := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (q ^ 2 + q + 2))) U
  have hC := Finset.card_sdiff_add_card_inter S U
  have hSet : (Finset.univ \ U) ∩ S = S \ U := by ext v; simp [and_comm]
  rw [hSet] at hA
  simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hB
  rw [Finset.inter_comm] at hC
  have hAInt : ((packingHoles q G P).card : ℤ) + (S \ U).card = (Finset.univ \ U).card := by exact_mod_cast hA
  have hBInt : ((Finset.univ \ U).card : ℤ) + U.card = (q : ℤ) ^ 2 + q + 2 := by exact_mod_cast hB
  have hCInt : ((S \ U).card : ℤ) + (U ∩ S).card = S.card := by exact_mod_cast hC
  have hCovered : (U.card : ℤ) = (q : ℤ) * P.card - ∑ t ∈ P, (signedDeficiency q G t - 1) := by
    rw [open_packing_covered_card G P hOpen]
    simp [signedDeficiency, Finset.sum_sub_distrib, mul_comm]
    ring
  change ((packingHoles q G P).card : ℤ) = _ + 2 - S.card + _ + (U ∩ S).card
  nlinarith

/-- The excess forces many unit rows unless the outside low weight is small. -/
theorem packing_unit_rows_excess_lower (q a : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G) :
    (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) + 2 * a + 2 -
      2 * ((q : ℤ) + 2 - P.card) - (highVertices q G).card ≤ (packingUnitRows q G P).card := by
  have hUnit := packing_unit_rows_lower q G P hLow
  have hSplit := Finset.sum_sdiff (f := signedDeficiency q G) hLow
  rw [lowVertices_signed_sum, total_positiveDeficiency_eq_signed_add_high q G hDegree, hTotal] at hSplit
  have hTau : (∑ t ∈ P, (signedDeficiency q G t - 1)) = (∑ t ∈ P, signedDeficiency q G t) - P.card := by
    simp [Finset.sum_sub_distrib]
  linarith

/-- A deficit of at least three creates many holes, including the covered outside lows. -/
theorem packing_holes_excess_lower (q a : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    ((q : ℤ) - 1 - P.card) * q + 2 * a +
      (packingCovered G P ∩ (lowVertices q G \ P)).card - (highVertices q G).card ≤ (packingHoles q G P).card := by
  have hIdentity := packing_holes_card_identity q G P hOpen
  have hLowWeight := low_card_add_packing_excess_le q G P hLow
  rw [total_positiveDeficiency_eq_signed_add_high q G hDegree, hTotal] at hLowWeight
  have hTau := packing_excess_nonnegative q G P hLow
  have hIncidence : ((packingCovered G P ∩ (lowVertices q G \ P)).card : ℤ) ≤
      (packingCovered G P ∩ lowVertices q G).card := by
    exact_mod_cast Finset.card_le_card (show packingCovered G P ∩ (lowVertices q G \ P) ⊆ packingCovered G P ∩ lowVertices q G from
      fun _ hv => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).1⟩)
  nlinarith

theorem packing_holes_spec {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n))
    (v : Fin n) (hv : v ∈ packingHoles q G P) :
    q + 1 ≤ G.degree v ∧ ∀ t ∈ P, ¬G.Adj v t := by
  have hvNotLow := (Finset.mem_sdiff.mp hv).2
  have hvNotCovered := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
  constructor
  · have hNonpositive : signedDeficiency q G v ≤ 0 := by
      by_contra h
      exact hvNotLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
    unfold signedDeficiency at hNonpositive
    omega
  · intro t ht hAdj
    apply hvNotCovered
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨t, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v t).mpr hAdj, ht⟩⟩⟩

/-- A higher-degree nonneighbor has a neighbor with zero codegree from the selected vertex. -/
theorem exists_zero_codegree_neighbor_of_degree_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (t v : Fin n) (hNot : ¬G.Adj t v)
    (hDegree : G.degree t < G.degree v) :
    ∃ w, G.Adj v w ∧ codegree G t w = 0 := by
  by_contra h
  have hPositive (w) (hw : w ∈ G.neighborFinset v) : 1 ≤ codegree G t w := by
    have hAdj := (G.mem_neighborFinset v w).mp hw
    have hNe : codegree G t w ≠ 0 := fun hZero => h ⟨w, hAdj, hZero⟩
    omega
  have hLower : G.degree v ≤ ∑ w ∈ G.neighborFinset v, codegree G t w := by
    calc
      _ = ∑ _w ∈ G.neighborFinset v, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hPositive
  have hExchange : (∑ w ∈ G.neighborFinset v, codegree G t w) =
      ∑ w ∈ G.neighborFinset t, codegree G v w := by
    simpa only [codegree, Finset.inter_comm] using sum_neighbor_intersection_card G (G.neighborFinset v) (G.neighborFinset t)
  have hUpper : (∑ w ∈ G.neighborFinset t, codegree G v w) ≤ G.degree t := by
    calc
      _ ≤ ∑ _w ∈ G.neighborFinset t, 1 := by
        apply Finset.sum_le_sum
        intro w hw
        have hNe : v ≠ w := by
          intro hEq
          exact hNot ((G.mem_neighborFinset t v).mp (hEq ▸ hw))
        exact codegree_le_one G hFree v w hNe
      _ = _ := by simp
  omega

/-- Each hole meets the outside zero partners of every unit packing row. -/
theorem packing_hole_meets_unit_zero_partners (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2))) (t : Fin (q ^ 2 + q + 2)) (ht : t ∈ packingUnitRows q G P)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ packingHoles q G P) :
    ∃ w ∈ (zeroCodegreeGraph G).neighborFinset t \ P, G.Adj v w := by
  obtain ⟨hvDegree, hvNot⟩ := packing_holes_spec q G P v hv
  obtain ⟨htP, htUnit⟩ := Finset.mem_filter.mp ht
  have htDegree : G.degree t = q := by unfold signedDeficiency at htUnit; omega
  obtain ⟨w, hvw, hZero⟩ := exists_zero_codegree_neighbor_of_degree_lt G hFree t v
    (fun h => hvNot t htP h.symm) (by omega)
  have hNe : t ≠ w := by intro h; exact hvNot t htP (h ▸ hvw)
  have hwNot : w ∉ P := fun hw => hvNot w hw hvw
  exact ⟨w, Finset.mem_sdiff.mpr ⟨((zeroCodegreeGraph G).mem_neighborFinset t w).mpr ⟨hNe, hZero⟩, hwNot⟩, hvw⟩


/-- Adjacent light vertices whose common-neighbor count with the row is zero. -/
def untriangulatedLightPartners {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n)) (t : Fin n) : Finset (Fin n) :=
  (G.neighborFinset t ∩ boundedLightLowVertices q T G).filter fun v => codegree G t v = 0

/-- Count the covered vertices in any selected set. -/
theorem open_packing_covered_intersection_card {n : ℕ} (G : SimpleGraph (Fin n))
    (P X : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    (∑ t ∈ P, (G.neighborFinset t ∩ X).card) = (packingCovered G P ∩ X).card := by
  have hCount := sum_neighbor_intersection_card G P X
  have hCountInt : (∑ t ∈ P, ((G.neighborFinset t ∩ X).card : ℤ)) =
      ∑ v ∈ X, ((G.neighborFinset v ∩ P).card : ℤ) := by exact_mod_cast hCount
  simp_rw [open_packing_neighbor_indicator G P hOpen] at hCountInt
  rw [← Finset.sum_filter] at hCountInt
  have hSet : (X.filter fun v => v ∈ packingCovered G P) = packingCovered G P ∩ X := by
    ext v
    simp [and_comm]
  rw [hSet] at hCountInt
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hCountInt
  exact_mod_cast hCountInt

/-- The outside zero partners of a selected row are determined by its deficiency. -/
theorem open_packing_outside_zero_row_identity (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2)))
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (t : Fin (q ^ 2 + q + 2)) (ht : t ∈ P) :
    (((zeroCodegreeGraph G).neighborFinset t \ P).card : ℤ) =
      (q : ℤ) + 2 - P.card + q * (signedDeficiency q G t - 1) +
        ∑ v ∈ G.neighborFinset t, signedDeficiency q G v := by
  have hParts : (((zeroCodegreeGraph G).neighborFinset t \ P).card : ℤ) +
      ((zeroCodegreeGraph G).neighborFinset t ∩ P).card = (zeroCodegreeGraph G).degree t := by
    exact_mod_cast Finset.card_sdiff_add_card_inter ((zeroCodegreeGraph G).neighborFinset t) P
  have hInside : (((zeroCodegreeGraph G).neighborFinset t ∩ P).card : ℤ) + 1 = P.card := by
    exact_mod_cast open_packing_zero_neighbors_inside G P hOpen t ht
  have hRow := zeroCodegree_degree_identity q G hFree t
  nlinarith

theorem untriangulatedLightPartners_subset {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hP : P ⊆ boundedNonlightLowVertices q T G) (t : Fin n) :
    untriangulatedLightPartners q T G t ⊆ (zeroCodegreeGraph G).neighborFinset t \ P := by
  intro v hv
  obtain ⟨hvN, hvLight⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp hv).1
  have hAdj := (G.mem_neighborFinset t v).mp hvN
  have hZero := (Finset.mem_filter.mp hv).2
  have hNot : v ∉ P := fun h => (Finset.mem_sdiff.mp (hP h)).2 hvLight
  exact Finset.mem_sdiff.mpr ⟨((zeroCodegreeGraph G).mem_neighborFinset t v).mpr ⟨hAdj.ne, hZero⟩, hNot⟩

/-- All adjacent lights are either untriangulated partners or triangular light neighbors. -/
theorem light_neighbors_card_le_untriangulated_add_triangular (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G) (t : Fin (q ^ 2 + q + 2)) :
    (G.neighborFinset t ∩ boundedLightLowVertices q T G).card ≤
      (untriangulatedLightPartners q T G t).card + (boundedTriangularLightNeighbors q T G t).card := by
  have hSubset : G.neighborFinset t ∩ boundedLightLowVertices q T G ⊆
      untriangulatedLightPartners q T G t ∪ boundedTriangularLightNeighbors q T G t := by
    intro v hv
    have hAdj := (G.mem_neighborFinset t v).mp (Finset.mem_inter.mp hv).1
    have hBound := codegree_le_one G hFree t v hAdj.ne
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hBound with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2, h⟩)
  exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)

/-- A unit row has only boundedly many outside zero partners beyond its adjacent lights. -/
theorem unit_row_remaining_zero_partners_le (q T K M J J₀ H : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hJ : (boundedLightTriangleRegularVertices q T G).card ≤ J₀) (hHigh : (highVertices q G).card ≤ H)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hGap : q + 2 ≤ P.card + J) (t : Fin (q ^ 2 + q + 2)) (ht : t ∈ packingUnitRows q G P) :
    (((zeroCodegreeGraph G).neighborFinset t \ P) \ untriangulatedLightPartners q T G t).card ≤
      J + K * M + J₀ + H + M := by
  obtain ⟨htP, htUnit⟩ := Finset.mem_filter.mp ht
  have hRow := open_packing_outside_zero_row_identity q G hFree P hOpen t htP
  rw [htUnit, sub_self, mul_zero, add_zero] at hRow
  have hSigned : (∑ v ∈ G.neighborFinset t, signedDeficiency q G v) ≤
      ∑ v ∈ G.neighborFinset t, positiveDeficiency q G v := Finset.sum_le_sum (fun v _ => le_max_left _ _)
  have hWeight := bounded_neighbor_positive_weight q T (K : ℤ) (Int.natCast_nonneg K) G hGlobal t
  have hTriangle := bounded_triangular_light_neighbor_card_le q T G hFree hIndependent t
  have hLight := light_neighbors_card_le_untriangulated_add_triangular q T G hFree t
  have hPart := Finset.card_sdiff_add_card_eq_card (untriangulatedLightPartners_subset q T G P hP t)
  have hGapInt : (q : ℤ) + 2 ≤ P.card + J := by exact_mod_cast hGap
  have hNonlightInt : ((G.neighborFinset t ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤ M := by exact_mod_cast hNonlight t
  have hTriangleInt : ((boundedTriangularLightNeighbors q T G t).card : ℤ) ≤ J₀ + H + M := by
    exact_mod_cast hTriangle.trans (Nat.add_le_add (Nat.add_le_add hJ hHigh) (hNonlight t))
  have hLightInt : ((G.neighborFinset t ∩ boundedLightLowVertices q T G).card : ℤ) ≤
      (untriangulatedLightPartners q T G t).card + (boundedTriangularLightNeighbors q T G t).card := by exact_mod_cast hLight
  have hPartInt : ((((zeroCodegreeGraph G).neighborFinset t \ P) \ untriangulatedLightPartners q T G t).card : ℤ) +
      (untriangulatedLightPartners q T G t).card = ((zeroCodegreeGraph G).neighborFinset t \ P).card := by exact_mod_cast hPart
  have hScaled := mul_le_mul_of_nonneg_left hNonlightInt (Int.natCast_nonneg K)
  have hResult : ((((zeroCodegreeGraph G).neighborFinset t \ P) \ untriangulatedLightPartners q T G t).card : ℤ) ≤
      J + (K : ℤ) * M + J₀ + H + M := by linarith
  exact_mod_cast hResult

/-- Every light has only boundedly many neighbors among the holes of an almost full packing. -/
theorem light_hole_neighbors_card_le (q T E J : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hGap : q + 2 ≤ P.card + J)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E)
    (l : Fin (q ^ 2 + q + 2)) (hl : l ∈ boundedLightLowVertices q T G) :
    (G.neighborFinset l ∩ packingHoles q G P).card ≤ J + E := by
  have hUnit := (Finset.mem_filter.mp hl).2.1
  have hLow := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hl).1).1
  have hNot : l ∉ P := fun h => (Finset.mem_sdiff.mp (hP h)).2 hl
  have hDegree : G.degree l = q := by unfold signedDeficiency at hUnit; omega
  have hRow := open_packing_covered_neighbors_outside G hFree P hOpen l hNot
  have hPart := Finset.card_sdiff_add_card_inter (G.neighborFinset l) (packingCovered G P)
  rw [SimpleGraph.card_neighborFinset_eq_degree, hDegree] at hPart
  have hZero := hOutside l hLow hNot
  have hSubset : G.neighborFinset l ∩ packingHoles q G P ⊆ G.neighborFinset l \ packingCovered G P := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).1,
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).1).2⟩
  have hCount := Finset.card_le_card hSubset
  have hPartInt : ((G.neighborFinset l \ packingCovered G P).card : ℤ) +
      (G.neighborFinset l ∩ packingCovered G P).card = q := by exact_mod_cast hPart
  have hZeroInt : (((zeroCodegreeGraph G).neighborFinset l ∩ P).card : ℤ) ≤ E := by exact_mod_cast hZero
  have hGapInt : (q : ℤ) + 2 ≤ P.card + J := by exact_mod_cast hGap
  have hOutsideBound : (G.neighborFinset l \ packingCovered G P).card ≤ J + E := by
    exact_mod_cast (show ((G.neighborFinset l \ packingCovered G P).card : ℤ) ≤ J + E by omega)
  exact hCount.trans hOutsideBound

/-- The adjacent light partners over all unit rows are covered outside low vertices. -/
theorem unit_light_partners_total_le (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (P : Finset (Fin (q ^ 2 + q + 2)))
    (hP : P ⊆ boundedNonlightLowVertices q T G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    (∑ t ∈ packingUnitRows q G P, (untriangulatedLightPartners q T G t).card) ≤
      (packingCovered G P ∩ (lowVertices q G \ P)).card := by
  have hEach (t) : untriangulatedLightPartners q T G t ⊆ G.neighborFinset t ∩ (lowVertices q G \ P) := by
    intro v hv
    obtain ⟨hvN, hvLight⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp hv).1
    have hvLow := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvLight).1).1
    have hvNot : v ∉ P := fun h => (Finset.mem_sdiff.mp (hP h)).2 hvLight
    exact Finset.mem_inter.mpr ⟨hvN, Finset.mem_sdiff.mpr ⟨hvLow, hvNot⟩⟩
  calc
    _ ≤ ∑ t ∈ packingUnitRows q G P, (G.neighborFinset t ∩ (lowVertices q G \ P)).card :=
      Finset.sum_le_sum (fun t _ => Finset.card_le_card (hEach t))
    _ ≤ ∑ t ∈ P, (G.neighborFinset t ∩ (lowVertices q G \ P)).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = _ := open_packing_covered_intersection_card G P (lowVertices q G \ P) hOpen


/-- A cover by a bounded residual family forces a heavy residual neighbor unless the light part is large. -/
theorem cover_forces_heavy_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (U A B : Finset (Fin n)) (L R : ℕ) (hR : 1 ≤ R) (hU : U.Nonempty)
    (hA : ∀ v ∈ A, (G.neighborFinset v ∩ U).card ≤ L) (hB : B.card ≤ R)
    (hCover : ∀ u ∈ U, ∃ v ∈ A ∪ B, G.Adj u v) :
    U.card ≤ 2 * L * A.card ∨ ∃ v ∈ B, U.card ≤ 2 * R * (G.neighborFinset v ∩ U).card := by
  by_cases hLight : U.card ≤ 2 * L * A.card
  · exact Or.inl hLight
  apply Or.inr
  by_contra h
  have hPositive : 1 ≤ U.card := Finset.card_pos.mpr hU
  have hSmall (v) (hv : v ∈ B) : 2 * R * (G.neighborFinset v ∩ U).card ≤ U.card - 1 := by
    have hNot : ¬U.card ≤ 2 * R * (G.neighborFinset v ∩ U).card := fun hc => h ⟨v, hv, hc⟩
    omega
  have hIncidence : U.card ≤ (∑ v ∈ A, (G.neighborFinset v ∩ U).card) +
      ∑ v ∈ B, (G.neighborFinset v ∩ U).card := by
    have hPoint (u) (hu : u ∈ U) : 1 ≤ (G.neighborFinset u ∩ A).card + (G.neighborFinset u ∩ B).card := by
      obtain ⟨v, hv, huv⟩ := hCover u hu
      rcases Finset.mem_union.mp hv with hvA | hvB
      · have hPos : 1 ≤ (G.neighborFinset u ∩ A).card := Finset.card_pos.mpr
          ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv, hvA⟩⟩
        omega
      · have hPos : 1 ≤ (G.neighborFinset u ∩ B).card := Finset.card_pos.mpr
          ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv, hvB⟩⟩
        omega
    have hSum := Finset.sum_le_sum hPoint
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_add_distrib,
      sum_neighbor_intersection_card G U A, sum_neighbor_intersection_card G U B] using hSum
  have hLightSum : (∑ v ∈ A, (G.neighborFinset v ∩ U).card) ≤ L * A.card := by
    calc
      _ ≤ ∑ _v ∈ A, L := Finset.sum_le_sum hA
      _ = _ := by simp [Nat.mul_comm]
  have hScaled : 2 * R * (∑ v ∈ B, (G.neighborFinset v ∩ U).card) ≤ R * (U.card - 1) := by
    calc
      _ = ∑ v ∈ B, 2 * R * (G.neighborFinset v ∩ U).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _v ∈ B, (U.card - 1) := Finset.sum_le_sum hSmall
      _ = B.card * (U.card - 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right (U.card - 1) hB
  have hResidual : 2 * (∑ v ∈ B, (G.neighborFinset v ∩ U).card) ≤ U.card - 1 := by
    by_contra hNot
    have hStep : U.card ≤ 2 * (∑ v ∈ B, (G.neighborFinset v ∩ U).card) := by omega
    have hMul := Nat.mul_le_mul_left R hStep
    nlinarith
  have hLight' : 2 * (L * A.card) < U.card := by
    simpa only [mul_assoc] using Nat.lt_of_not_ge hLight
  omega

/-- Only a bounded number of vertices can meet a fixed positive fraction of a large hole set. -/
theorem many_hole_neighbors_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (U W : Finset (Fin n)) (R : ℕ) (hR : 1 ≤ R)
    (hOrder : 6 * (2 * R) ^ 2 ≤ U.card)
    (hHeavy : ∀ w ∈ W, U.card ≤ 2 * R * (G.neighborFinset w ∩ U).card) :
    W.card ≤ 18 * (2 * R) ^ 2 := by
  have hPositive : 0 < U.card := by nlinarith
  have hBound := finite_family_card_le W U (fun w => G.neighborFinset w ∩ U)
    (U.card : ℤ) (2 * R : ℤ) 1
    (by exact_mod_cast hPositive) (by exact_mod_cast (show 1 ≤ 2 * R by omega)) (by norm_num)
    (fun _ _ => Finset.inter_subset_right)
    (by omega)
    (fun w hw => by exact_mod_cast hHeavy w hw)
    (by
      intro w _ v _ hNe
      have hSubset : (G.neighborFinset w ∩ U) ∩ (G.neighborFinset v ∩ U) ⊆
          G.neighborFinset w ∩ G.neighborFinset v := by
        intro t ht
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp ht).1).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp ht).2).1⟩
      have hCard := (Finset.card_le_card hSubset).trans (codegree_le_one G hFree w v hNe)
      exact_mod_cast hCard)
    (by
      rw [mul_one]
      exact_mod_cast hOrder)
  exact_mod_cast hBound

/-- Weighted incidences exceed their total weight only through pairs of centers. -/
theorem weighted_incidence_le_weight_add_pairs {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (X W : Finset (Fin n)) (a : Fin n → ℤ) (K : ℤ) (hK : 0 ≤ K)
    (ha : ∀ v ∈ X, 0 ≤ a v) (hCap : ∀ v ∈ X, a v ≤ K) :
    (∑ v ∈ X, a v * (G.neighborFinset v ∩ W).card) ≤
      (∑ v ∈ X, a v) + K * (W.card : ℤ) ^ 2 := by
  have hPoint (v) (hv : v ∈ X) : a v * (G.neighborFinset v ∩ W).card ≤
      a v + K * (((G.neighborFinset v ∩ W).card : ℤ) ^ 2 - (G.neighborFinset v ∩ W).card) := by
    have hNonneg : (0 : ℤ) ≤ (G.neighborFinset v ∩ W).card := Int.natCast_nonneg _
    by_cases hSmall : (G.neighborFinset v ∩ W).card ≤ 1
    · have hCases := Nat.le_one_iff_eq_zero_or_eq_one.mp hSmall
      rcases hCases with h | h <;> simp only [h, Nat.cast_zero, Nat.cast_one, one_pow, mul_zero, mul_one, sub_self, add_zero] <;> linarith [ha v hv]
    · have hLarge : (1 : ℤ) ≤ (G.neighborFinset v ∩ W).card := by exact_mod_cast (show 1 ≤ (G.neighborFinset v ∩ W).card by omega)
      have hFactor := mul_nonneg (sub_nonneg.mpr (hCap v hv)) (sub_nonneg.mpr hLarge)
      have hExtra := mul_nonneg hK (mul_nonneg (sub_nonneg.mpr hLarge) (sub_nonneg.mpr hLarge))
      nlinarith
  have hSum := Finset.sum_le_sum hPoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hSum
  have hCoverage := restricted_pair_coverage_le G hFree W X
  have hScaled := mul_le_mul_of_nonneg_left hCoverage hK
  have hDrop : 0 ≤ K * (W.card : ℤ) := mul_nonneg hK (Int.natCast_nonneg _)
  nlinarith


/-- A bounded family of connectors has only bounded repeated low weight beyond the outside low total. -/
theorem open_packing_positive_incidence_sum_le (q K : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (P W : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    (∑ w ∈ W, ∑ v ∈ G.neighborFinset w, positiveDeficiency q G v) ≤
      (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) + K * (W.card : ℤ) + K * (W.card : ℤ) ^ 2 := by
  let d : Fin (q ^ 2 + q + 2) → ℤ := fun v => (G.neighborFinset v ∩ W).card
  have hTerm (v) : d v * positiveDeficiency q G v =
      if v ∈ lowVertices q G then d v * signedDeficiency q G v else 0 := by
    by_cases hLowV : v ∈ lowVertices q G
    · have hPositive := (Finset.mem_filter.mp hLowV).2
      rw [ite_eq_left hLowV, positiveDeficiency, max_eq_left (le_of_lt hPositive)]
    · have hNonpositive : signedDeficiency q G v ≤ 0 := by
        by_contra h
        exact hLowV (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      rw [ite_eq_right hLowV, positiveDeficiency, max_eq_right hNonpositive, mul_zero]
  have hSupport : (∑ v, d v * positiveDeficiency q G v) =
      ∑ v ∈ lowVertices q G, d v * signedDeficiency q G v := by
    simp_rw [hTerm]
    rw [← Finset.sum_filter]
    have hSet : (Finset.univ.filter fun v => v ∈ lowVertices q G) = lowVertices q G := by ext v; simp
    rw [hSet]
  have hSplit := Finset.sum_sdiff (f := fun v => d v * signedDeficiency q G v) hLow
  have hPWeight : (∑ v ∈ P, d v * signedDeficiency q G v) ≤ (K : ℤ) * W.card := by
    have hBound : (∑ v ∈ P, d v * signedDeficiency q G v) ≤ (K : ℤ) * (∑ v ∈ P, d v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      have h := mul_le_mul_of_nonneg_left (hGlobal v) (show 0 ≤ d v by dsimp [d]; positivity)
      simpa only [mul_comm] using h
    have hCount : (∑ v ∈ P, d v) ≤ W.card := by
      have hExchange : (∑ v ∈ P, d v) = ∑ w ∈ W, ((G.neighborFinset w ∩ P).card : ℤ) := by
        dsimp only [d]
        exact_mod_cast sum_neighbor_intersection_card G P W
      rw [hExchange]
      calc
        _ ≤ ∑ _w ∈ W, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro w _
          exact_mod_cast open_packing_neighbor_card_le_one G P hOpen w
        _ = _ := by simp
    exact hBound.trans (mul_le_mul_of_nonneg_left hCount (Int.natCast_nonneg K))
  have hXWeight : (∑ v ∈ lowVertices q G \ P, d v * signedDeficiency q G v) ≤
      (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) + (K : ℤ) * (W.card : ℤ) ^ 2 := by
    have h := weighted_incidence_le_weight_add_pairs G hFree (lowVertices q G \ P) W
      (signedDeficiency q G) K (Int.natCast_nonneg K)
      (fun v hv => le_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2)
      (fun v _ => hGlobal v)
    simpa only [d, mul_comm] using h
  rw [sum_selected_neighbor_weights]
  change (∑ v, d v * positiveDeficiency q G v) ≤ _
  rw [hSupport]
  linarith

/-- Outside zero-partner columns are bounded by the low-column cap and positive neighbor weight. -/
theorem outside_zero_partner_column_card_le (q E : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P S : Finset (Fin (q ^ 2 + q + 2))) (hS : S ⊆ P)
    (B : Fin (q ^ 2 + q + 2) → Finset (Fin (q ^ 2 + q + 2)))
    (hB : ∀ t ∈ S, B t ⊆ (zeroCodegreeGraph G).neighborFinset t \ P)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E)
    (w : Fin (q ^ 2 + q + 2)) :
    ((S.filter fun t => w ∈ B t).card : ℤ) ≤
      E + 1 + ∑ v ∈ G.neighborFinset w, positiveDeficiency q G v := by
  have hNonnegative : 0 ≤ ∑ v ∈ G.neighborFinset w, positiveDeficiency q G v :=
    Finset.sum_nonneg (fun v _ => positiveDeficiency_nonnegative q G v)
  by_cases hw : w ∈ P
  · have hEmpty : (S.filter fun t => w ∈ B t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨htS, htB⟩ := Finset.mem_filter.mp ht
      exact (Finset.mem_sdiff.mp (hB t htS htB)).2 hw
    rw [hEmpty, Finset.card_empty, Nat.cast_zero]
    positivity
  have hSubset : (S.filter fun t => w ∈ B t) ⊆ (zeroCodegreeGraph G).neighborFinset w ∩ P := by
    intro t ht
    obtain ⟨htS, htB⟩ := Finset.mem_filter.mp ht
    have hAdj := ((zeroCodegreeGraph G).mem_neighborFinset t w).mp (Finset.mem_sdiff.mp (hB t htS htB)).1
    exact Finset.mem_inter.mpr ⟨((zeroCodegreeGraph G).mem_neighborFinset w t).mpr hAdj.symm, hS htS⟩
  have hCount : ((S.filter fun t => w ∈ B t).card : ℤ) ≤ ((zeroCodegreeGraph G).neighborFinset w ∩ P).card := by
    exact_mod_cast Finset.card_le_card hSubset
  by_cases hLow : w ∈ lowVertices q G
  · have hLowBound : (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ) ≤ E := by
      exact_mod_cast hOutside w hLow hw
    linarith
  · have hNonpositive : signedDeficiency q G w ≤ 0 := by
      by_contra h
      exact hLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
    have hRow := zeroCodegree_degree_identity q G hFree w
    have hCard : (((zeroCodegreeGraph G).neighborFinset w ∩ P).card : ℤ) ≤ (zeroCodegreeGraph G).degree w := by
      exact_mod_cast (show ((zeroCodegreeGraph G).neighborFinset w ∩ P).card ≤ (zeroCodegreeGraph G).degree w by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card
          (Finset.inter_subset_left : (zeroCodegreeGraph G).neighborFinset w ∩ P ⊆ (zeroCodegreeGraph G).neighborFinset w))
    have hWeighted : (∑ v ∈ G.neighborFinset w, signedDeficiency q G v) ≤
        ∑ v ∈ G.neighborFinset w, positiveDeficiency q G v := Finset.sum_le_sum (fun v _ => le_max_left _ _)
    have hProduct : (q : ℤ) * signedDeficiency q G w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg q) hNonpositive
    linarith


/-- Covering a large hole set bounds the number of rows by their outside low weight and fixed errors. -/
theorem hole_cover_row_bound {n : ℕ} (G : SimpleGraph (Fin n)) (hFree : (cycleGraph 4).Free G)
    (U S : Finset (Fin n)) (A B : Fin n → Finset (Fin n)) (L R E K : ℕ) (F : ℤ) (c : Fin n → ℤ)
    (hR : 1 ≤ R) (hOrder : 6 * (2 * R) ^ 2 ≤ U.card)
    (hLight : ∀ t ∈ S, ∀ v ∈ A t, (G.neighborFinset v ∩ U).card ≤ L)
    (hSmall : ∀ t ∈ S, (B t).card ≤ R)
    (hTotalLight : (∑ t ∈ S, (A t).card) ≤ 2 * U.card)
    (hCover : ∀ t ∈ S, ∀ u ∈ U, ∃ v ∈ A t ∪ B t, G.Adj u v)
    (hColumn : ∀ w, ((S.filter fun t => w ∈ B t).card : ℤ) ≤ E + 1 + c w)
    (hWeight : ∀ W : Finset (Fin n), (∑ w ∈ W, c w) ≤ F + K * (W.card : ℤ) + K * (W.card : ℤ) ^ 2) :
    (S.card : ℤ) ≤ F + 4 * L + ((E : ℤ) + 1 + K) * (18 * (2 * (R : ℤ)) ^ 2) +
      K * (18 * (2 * (R : ℤ)) ^ 2) ^ 2 := by
  let W := Finset.univ.filter fun w => U.card ≤ 2 * R * (G.neighborFinset w ∩ U).card
  let S₀ := S.filter fun t => U.card ≤ 2 * L * (A t).card
  let S₁ := S \ S₀
  let N : ℕ := 18 * (2 * R) ^ 2
  have hU : U.Nonempty := by
    apply Finset.card_pos.mp
    nlinarith
  have hW : W.card ≤ N := many_hole_neighbors_card_le G hFree U W R hR hOrder
    (fun w hw => (Finset.mem_filter.mp hw).2)
  have hS₀ : S₀ ⊆ S := Finset.filter_subset _ _
  have hS₁ : S₁ ⊆ S := Finset.sdiff_subset
  have hSmallProduct : S₀.card * U.card ≤ 4 * L * U.card := by
    have hRows : S₀.card * U.card ≤ 2 * L * (∑ t ∈ S₀, (A t).card) := by
      have h := Finset.sum_le_sum (fun t (ht : t ∈ S₀) => (Finset.mem_filter.mp ht).2)
      simpa only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] using h
    have hSubset := Finset.sum_le_sum_of_subset hS₀ (f := fun t => (A t).card)
    have hScaled := Nat.mul_le_mul_left (2 * L) (hSubset.trans hTotalLight)
    nlinarith
  have hSmallCard : (S₀.card : ℤ) ≤ 4 * L := by
    have hUPos : (0 : ℤ) < U.card := by exact_mod_cast Finset.card_pos.mpr hU
    apply (mul_le_mul_iff_of_pos_right hUPos).mp
    exact_mod_cast hSmallProduct
  have hWitness (t) (ht : t ∈ S₁) : ∃ w ∈ W, w ∈ B t := by
    have htS := hS₁ ht
    have hAlt := cover_forces_heavy_neighbor G U (A t) (B t) L R hR hU (hLight t htS) (hSmall t htS) (hCover t htS)
    rcases hAlt with hAlt | ⟨w, hwB, hwHeavy⟩
    · have htNot := (Finset.mem_sdiff.mp ht).2
      exact False.elim (htNot (Finset.mem_filter.mpr ⟨htS, hAlt⟩))
    · exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwHeavy⟩, hwB⟩
  have hGoodCount : S₁.card ≤ ∑ w ∈ W, (S₁.filter fun t => w ∈ B t).card := by
    calc
      _ = ∑ _t ∈ S₁, 1 := by simp
      _ ≤ ∑ t ∈ S₁, (W.filter fun w => w ∈ B t).card := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨w, hwW, hwB⟩ := hWitness t ht
        exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwW, hwB⟩⟩
      _ = ∑ t ∈ S₁, ∑ w ∈ W, if w ∈ B t then (1 : ℕ) else 0 := by simp only [Finset.sum_boole, Nat.cast_id]
      _ = ∑ w ∈ W, ∑ t ∈ S₁, if w ∈ B t then (1 : ℕ) else 0 := Finset.sum_comm
      _ = _ := by simp only [Finset.sum_boole, Nat.cast_id]
  have hColumnGood (w) : ((S₁.filter fun t => w ∈ B t).card : ℤ) ≤ E + 1 + c w := by
    have hSubset : (S₁.filter fun t => w ∈ B t) ⊆ (S.filter fun t => w ∈ B t) := by
      intro t ht
      obtain ⟨htS₁, htB⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨hS₁ htS₁, htB⟩
    have hCount : ((S₁.filter fun t => w ∈ B t).card : ℤ) ≤ (S.filter fun t => w ∈ B t).card := by
      exact_mod_cast Finset.card_le_card hSubset
    exact hCount.trans (hColumn w)
  have hGoodInt : (S₁.card : ℤ) ≤ ∑ w ∈ W, ((S₁.filter fun t => w ∈ B t).card : ℤ) := by exact_mod_cast hGoodCount
  have hGoodBound : (S₁.card : ℤ) ≤ ((E : ℤ) + 1) * W.card + ∑ w ∈ W, c w := by
    have hSum := Finset.sum_le_sum (fun w (_ : w ∈ W) => hColumnGood w)
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hSum
    nlinarith
  have hWInt : (W.card : ℤ) ≤ N := by exact_mod_cast hW
  have hWSquare : (W.card : ℤ) ^ 2 ≤ (N : ℤ) ^ 2 := by nlinarith [Int.natCast_nonneg W.card]
  have hLinear := mul_le_mul_of_nonneg_left hWInt (show 0 ≤ (E : ℤ) + 1 + K by positivity)
  have hQuadratic := mul_le_mul_of_nonneg_left hWSquare (Int.natCast_nonneg K)
  have hPartition : (S₁.card : ℤ) + S₀.card = S.card := by exact_mod_cast Finset.card_sdiff_add_card_eq_card hS₀
  have hN : (N : ℤ) = 18 * (2 * (R : ℤ)) ^ 2 := by dsimp only [N]; push_cast; rfl
  rw [← hN]
  nlinarith [hWeight W]


/-- The hole-cover argument bounds unit rows by outside low weight and a fixed error. -/
theorem packing_unit_rows_hole_bound (q T K M E J J₀ H : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hJ : (boundedLightTriangleRegularVertices q T G).card ≤ J₀) (hHigh : (highVertices q G).card ≤ H)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hGap : q + 2 ≤ P.card + J)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) :
    let R : ℕ := J + K * M + J₀ + H + M + 1
    let N : ℕ := 18 * (2 * R) ^ 2
    6 * (2 * R) ^ 2 ≤ (packingHoles q G P).card →
    (packingCovered G P ∩ (lowVertices q G \ P)).card ≤ 2 * (packingHoles q G P).card →
    ((packingUnitRows q G P).card : ℤ) ≤
      (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) + 4 * ((J : ℤ) + E) +
        ((E : ℤ) + 1 + K) * (N : ℤ) + (K : ℤ) * (N : ℤ) ^ 2 := by
  dsimp only
  intro hOrder hEta
  let R : ℕ := J + K * M + J₀ + H + M + 1
  let A := untriangulatedLightPartners q T G
  let B := fun t => ((zeroCodegreeGraph G).neighborFinset t \ P) \ A t
  let c := fun w => ∑ v ∈ G.neighborFinset w, positiveDeficiency q G v
  have hLow : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  have hLight (t) (_ht : t ∈ packingUnitRows q G P) (v) (hv : v ∈ A t) :
      (G.neighborFinset v ∩ packingHoles q G P).card ≤ J + E := by
    have hvLight := (Finset.mem_inter.mp (Finset.mem_filter.mp hv).1).2
    exact light_hole_neighbors_card_le q T E J G hFree P hP hOpen hGap hOutside v hvLight
  have hSmall (t) (ht : t ∈ packingUnitRows q G P) : (B t).card ≤ R := by
    have h := unit_row_remaining_zero_partners_le q T K M J J₀ H G hFree hGlobal hIndependent hNonlight hJ hHigh P hP hOpen hGap t ht
    change (B t).card ≤ J + K * M + J₀ + H + M at h
    exact h.trans (Nat.le_succ _)
  have hLightTotal : (∑ t ∈ packingUnitRows q G P, (A t).card) ≤ 2 * (packingHoles q G P).card :=
    (unit_light_partners_total_le q T G P hP hOpen).trans hEta
  have hCover (t) (ht : t ∈ packingUnitRows q G P) (u) (hu : u ∈ packingHoles q G P) :
      ∃ v ∈ A t ∪ B t, G.Adj u v := by
    obtain ⟨v, hv, huv⟩ := packing_hole_meets_unit_zero_partners q G hFree P t ht u hu
    by_cases hA : v ∈ A t
    · exact ⟨v, Finset.mem_union_left _ hA, huv⟩
    · exact ⟨v, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hA⟩), huv⟩
  have hColumn (w) : (((packingUnitRows q G P).filter fun t => w ∈ B t).card : ℤ) ≤ E + 1 + c w := by
    exact outside_zero_partner_column_card_le q E G hFree P (packingUnitRows q G P) (Finset.filter_subset _ _) B
      (fun _ _ => Finset.sdiff_subset) hOutside w
  have hWeight (W : Finset (Fin (q ^ 2 + q + 2))) : (∑ w ∈ W, c w) ≤
      (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) + K * (W.card : ℤ) + K * (W.card : ℤ) ^ 2 :=
    open_packing_positive_incidence_sum_le q K G hFree hGlobal P W hLow hOpen
  have h := hole_cover_row_bound G hFree (packingHoles q G P) (packingUnitRows q G P) A B
    (J + E) R E K (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) c
    (by dsimp only [R]; omega) hOrder hLight hSmall hLightTotal hCover hColumn hWeight
  simpa only [R, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using h

/-- A sufficiently large edge excess rules out any deficit in the maximum packing. -/
theorem open_packing_card_eq_parameter (q T K M E J J₀ H a : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hJ : (boundedLightTriangleRegularVertices q T G).card ≤ J₀) (hHigh : (highVertices q G).card ≤ H)
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hCard : P.card ≤ q) (hGap : q + 2 ≤ P.card + J)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) :
    let R : ℕ := J + K * M + J₀ + H + M + 1
    let N : ℕ := 18 * (2 * R) ^ 2
    let C : ℕ := 4 * (J + E) + (E + 1 + K) * N + K * N ^ 2
    6 * (2 * R) ^ 2 + C + 2 * J + 2 * H + 1 < a → P.card = q := by
  dsimp only
  intro hLarge
  let R : ℕ := J + K * M + J₀ + H + M + 1
  let N : ℕ := 18 * (2 * R) ^ 2
  let C : ℕ := 4 * (J + E) + (E + 1 + K) * N + K * N ^ 2
  have hLarge' : 6 * (2 * R) ^ 2 + C + 2 * J + 2 * H + 1 < a := hLarge
  have hLow : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  by_contra hNot
  have hp : P.card + 1 ≤ q := by omega
  have hHoles := packing_holes_excess_lower q a G hDegree hTotal P hLow hOpen
  have hUnit := packing_unit_rows_excess_lower q a G hDegree hTotal P hLow
  have hpInt : (P.card : ℤ) + 1 ≤ q := by exact_mod_cast hp
  have hCoefficient : 0 ≤ (q : ℤ) - 1 - P.card := by omega
  have hProduct : 0 ≤ ((q : ℤ) - 1 - P.card) * q := mul_nonneg hCoefficient (Int.natCast_nonneg q)
  have hHighInt : ((highVertices q G).card : ℤ) ≤ H := by exact_mod_cast hHigh
  have hLargeInt : 6 * (2 * (R : ℤ)) ^ 2 + C + 2 * J + 2 * H + 1 < a := by exact_mod_cast hLarge'
  have hLower : 2 * (a : ℤ) + (packingCovered G P ∩ (lowVertices q G \ P)).card - H ≤ (packingHoles q G P).card := by
    linarith only [hHoles, hProduct, hHighInt]
  have hThreshold : 6 * (2 * R) ^ 2 + H < a := by omega
  have hThresholdInt : 6 * (2 * (R : ℤ)) ^ 2 + H < a := by exact_mod_cast hThreshold
  have hAmin : H < a := by omega
  have hAminInt : (H : ℤ) < a := by exact_mod_cast hAmin
  have hEtaNonnegative : (0 : ℤ) ≤ (packingCovered G P ∩ (lowVertices q G \ P)).card := Int.natCast_nonneg _
  have hHolesNonnegative : (0 : ℤ) ≤ (packingHoles q G P).card := Int.natCast_nonneg _
  have hANonnegative : (0 : ℤ) ≤ a := Int.natCast_nonneg _
  have hOrder : 6 * (2 * R) ^ 2 ≤ (packingHoles q G P).card := by
    exact_mod_cast (show 6 * (2 * (R : ℤ)) ^ 2 ≤ (packingHoles q G P).card by
      linarith only [hLower, hThresholdInt, hEtaNonnegative, hANonnegative])
  have hEta : (packingCovered G P ∩ (lowVertices q G \ P)).card ≤ 2 * (packingHoles q G P).card := by
    exact_mod_cast (show ((packingCovered G P ∩ (lowVertices q G \ P)).card : ℤ) ≤ 2 * (packingHoles q G P).card by
      linarith only [hLower, hAminInt, hANonnegative, hHolesNonnegative])
  have hUpper := packing_unit_rows_hole_bound q T K M E J J₀ H G hFree hGlobal hIndependent hNonlight hJ hHigh P hP hOpen hGap hOutside hOrder hEta
  have hUpper' : ((packingUnitRows q G P).card : ℤ) ≤ (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) + C := by
    simpa only [C, N, R, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, add_assoc] using hUpper
  have hGapInt : (q : ℤ) + 2 ≤ P.card + J := by exact_mod_cast hGap
  have hSmallA : 2 * (a : ℤ) + 2 ≤ C + 2 * J + H := by
    linarith only [hUnit, hUpper', hGapInt, hHighInt]
  have hABound : C + 2 * J + H < a := by omega
  have hABoundInt : (C : ℤ) + 2 * J + H < a := by exact_mod_cast hABound
  linarith only [hSmallA, hABoundInt, hANonnegative]


/-- The claimed bound forces a maximum low open packing of exactly q vertices. -/
theorem claimedBound_uniform_full_packing (hBound : ClaimedBound) :
    ∃ C K T M R Q E N : ℕ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ k : ℕ, N ≤ 2 ^ (2 * (k + 1)) →
      ∀ G : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2) (cycleGraph 4) →
        2 ^ (2 * (k + 1)) ≤ 4 * C * abovePlaneExcess (2 ^ (2 * (k + 1))) ^ 2 ∧
        (∀ v, G.degree v ≤ 2 ^ (2 * (k + 1)) + 2) ∧
        (highVertices (2 ^ (2 * (k + 1))) G).card ≤ 2611456 * C ∧
        (∑ v, positiveDeficiency (2 ^ (2 * (k + 1))) G v) ≤ 3 * (2 ^ (2 * (k + 1)) : ℕ) ∧
        (∀ v, signedDeficiency (2 ^ (2 * (k + 1))) G v ≤ K) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G,
          ∀ w ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G, ¬G.Adj l w) ∧
        (∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G).card ≤ M) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G,
          (triangularRegularNeighbors (2 ^ (2 * (k + 1))) G l).card ≤ 16 ∧
          (positivePartners (2 ^ (2 * (k + 1))) G l).card ≤ R) ∧
        (boundedLightTriangleRegularVertices (2 ^ (2 * (k + 1))) T G).card ≤ 72 ∧
        (∀ v, signedDeficiency (2 ^ (2 * (k + 1))) G v = 0 → (positivePartners (2 ^ (2 * (k + 1))) G v).card ≤ R) ∧
        (∀ v, 1 ≤ signedDeficiency (2 ^ (2 * (k + 1))) G v →
          ((positivePartners (2 ^ (2 * (k + 1))) G v).filter fun y => signedDeficiency (2 ^ (2 * (k + 1))) G y = 0 ∨
            y ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G).card ≤ Q) ∧
        ∃ P : Finset (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          P ⊆ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G ∧
          (zeroCodegreeGraph G).IsClique (P : Set _) ∧ P.card = 2 ^ (2 * (k + 1)) ∧
          (∀ A ⊆ lowVertices (2 ^ (2 * (k + 1))) G, (zeroCodegreeGraph G).IsClique (A : Set _) → A.card ≤ P.card) ∧
          (∀ v ∈ lowVertices (2 ^ (2 * (k + 1))) G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) ∧
          ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  obtain ⟨C, K, T, M, R, Q, E, D, N₀, hC, hK, _hD, hStructure⟩ := claimedBound_uniform_structured_open_packing hBound
  let H := 2611456 * C
  let J := (3 * E ^ 2 + H + 6 * K + 22 + 6 + 2 * H) * D ^ 2
  let F := J + K * M + 72 + H + M + 1
  let W := 18 * (2 * F) ^ 2
  let B := 4 * (J + E) + (E + 1 + K) * W + K * W ^ 2
  let A := 6 * (2 * F) ^ 2 + B + 2 * J + 2 * H + 1
  let cutoff := N₀ + 4 * C * A ^ 2 + 3
  refine ⟨C, K, T, M, R, Q, E, cutoff, hC, hK, ?_⟩
  intro k hk G hFree hEdges
  let q := 2 ^ (2 * (k + 1))
  let a := abovePlaneExcess q
  have hCutoff : cutoff ≤ q := hk
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hOrder : 4 * C * A ^ 2 < q := by dsimp only [cutoff] at hCutoff; omega
  have hq : 3 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  obtain ⟨hExcess, hDegree, hHigh, hPositive, hGlobal, hIndependent, hNonlight, hLights,
    hJ, hRegular, hGood, P, hPN, hClique, hLarge, hMaximum, hOutside, hDisjoint⟩ := hStructure k hN₀ G hFree hEdges
  change q ≤ 4 * C * a ^ 2 at hExcess
  have hLargeA : A < a := by
    by_contra h
    have hSmall : a ≤ A := by omega
    have hSquare : a ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hSmall 2
    have hScaled := Nat.mul_le_mul_left (4 * C) hSquare
    omega
  have hLow : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hPN hv)).1
  have hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0 := by
    intro v hv w hw hNe
    exact (hClique hv hw hNe).2
  have hEven : Even q := by
    refine ⟨2 ^ (2 * k + 1), ?_⟩
    dsimp only [q]
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    omega
  have hCard := extremal_low_open_packing_card_le q hq hEven G hFree hEdges P hLow hOpen
  have hExcessThree : 3 ≤ a := by
    have hA : 2 ≤ A := by dsimp only [A, B, W, F, J, H]; omega
    omega
  have hDense := extremal_density_of_excess q G hEdges hExcessThree
  have hGap : q + 2 ≤ P.card + J :=
    open_packing_card_gap_le q K E H D (by omega) G hFree hDense hDegree hGlobal hPositive hHigh P hLow hOpen hCard hLarge hOutside
  have hEdgeCount : G.edgeFinset.card = planeEdgeCount q + a := by
    have hPos : 0 < abovePlaneExcess q := by change 0 < a; omega
    unfold abovePlaneExcess at hPos
    change _ = planeEdgeCount q + abovePlaneExcess q
    rw [hEdges]
    unfold abovePlaneExcess
    change extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) = planeEdgeCount q + (extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) - planeEdgeCount q)
    omega
  have hTotal := signedDeficiency_sum_of_excess q a G hEdgeCount
  have hFull : P.card = q := open_packing_card_eq_parameter q T K M E J 72 H a G hFree hDegree hGlobal
    hIndependent hNonlight hJ hHigh hTotal P hPN hOpen hCard hGap hOutside hLargeA
  exact ⟨hExcess, hDegree, hHigh, hPositive, hGlobal, hIndependent, hNonlight, hLights,
    hJ, hRegular, hGood, P, hPN, hClique, hFull, hMaximum, hOutside, hDisjoint⟩


/-- At packing size q, inside deficiencies are one or two and every outside low is unit. -/
theorem extremal_full_packing_deficiencies (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hEdges : G.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4))
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q) :
    (∀ t ∈ P, signedDeficiency q G t = 1 ∨ signedDeficiency q G t = 2) ∧
      ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1 := by
  constructor
  · intro t ht
    have hParent := extremal_parent_degree_bound G hFree hEdges P hOpen t
    have hErase := Finset.card_erase_add_one ht
    have hPositive := (Finset.mem_filter.mp (hLow ht)).2
    unfold signedDeficiency at hPositive ⊢
    omega
  · intro v hv
    obtain ⟨hvLow, hvNot⟩ := Finset.mem_sdiff.mp hv
    have hParent := extremal_parent_degree_bound G hFree hEdges P hOpen v
    rw [Finset.erase_eq_of_notMem hvNot, hCard] at hParent
    have hPositive := (Finset.mem_filter.mp hvLow).2
    unfold signedDeficiency at hPositive ⊢
    omega

/-- Packing rows with a neighbor inside the packing. -/
def pairedPackingRows {n : ℕ} (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  P.filter fun t => (G.neighborFinset t ∩ P).Nonempty

/-- The induced matching degree sum counts exactly the paired rows. -/
theorem open_packing_internal_degree_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    (∑ t ∈ P, (G.neighborFinset t ∩ P).card) = (pairedPackingRows G P).card := by
  have hEach (t) (_ht : t ∈ P) : (G.neighborFinset t ∩ P).card =
      if (G.neighborFinset t ∩ P).Nonempty then 1 else 0 := by
    have hUpper := open_packing_neighbor_card_le_one G P hOpen t
    by_cases h : (G.neighborFinset t ∩ P).Nonempty
    · have hPositive := Finset.card_pos.mpr h
      rw [ite_eq_left h]
      omega
    · have hZero : (G.neighborFinset t ∩ P).card = 0 := by
        simpa only [Finset.card_eq_zero] using Finset.not_nonempty_iff_eq_empty.mp h
      simp only [hZero, ite_eq_right h]
  rw [Finset.sum_congr rfl hEach, ← Finset.sum_filter]
  simp [pairedPackingRows]

/-- A nonempty set of paired packing rows contains both endpoints of an edge. -/
theorem pairedPackingRows_card_eq_zero_or_two_le {n : ℕ} (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) :
    (pairedPackingRows G P).card = 0 ∨ 2 ≤ (pairedPackingRows G P).card := by
  by_cases hZero : (pairedPackingRows G P).card = 0
  · exact Or.inl hZero
  apply Or.inr
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hZero)
  obtain ⟨htP, hNeighbor⟩ := Finset.mem_filter.mp ht
  obtain ⟨w, hw⟩ := hNeighbor
  obtain ⟨htw, hwP⟩ := Finset.mem_inter.mp hw
  have hAdj := (G.mem_neighborFinset t w).mp htw
  have hwPaired : w ∈ pairedPackingRows G P := Finset.mem_filter.mpr
    ⟨hwP, ⟨t, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w t).mpr hAdj.symm, htP⟩⟩⟩
  have hSubset : {t, w} ⊆ pairedPackingRows G P := by
    intro v hv
    rcases Finset.mem_insert.mp hv with h | h
    · simpa only [h] using ht
    · have hEq : v = w := Finset.mem_singleton.mp h
      simpa only [hEq] using hwPaired
  have hCard := Finset.card_le_card hSubset
  simpa only [Finset.card_pair hAdj.ne] using hCard

/-- At full packing size, the summed excess counts the deep rows. -/
theorem full_packing_excess_eq_deep_card (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (P : Finset (Fin (q ^ 2 + q + 2)))
    (hInside : ∀ t ∈ P, signedDeficiency q G t = 1 ∨ signedDeficiency q G t = 2) :
    (∑ t ∈ P, (signedDeficiency q G t - 1)) = ((P.filter fun t => signedDeficiency q G t = 2).card : ℤ) := by
  have hEach (t) (ht : t ∈ P) : signedDeficiency q G t - 1 = if signedDeficiency q G t = 2 then 1 else 0 := by
    rcases hInside t ht with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hEach, ← Finset.sum_filter]
  simp


/-- The packing covers the sum of its degrees, written in deficiency coordinates. -/
theorem open_packing_covered_card_by_excess {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    ((packingCovered G P).card : ℤ) = (q : ℤ) * P.card - ∑ t ∈ P, (signedDeficiency q G t - 1) := by
  rw [open_packing_covered_card G P hOpen]
  simp [signedDeficiency, Finset.sum_sub_distrib]
  ring

/-- At full packing size, outside unit lows account exactly for the low-set cardinality. -/
theorem full_packing_low_card_add_excess {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hLow : P ⊆ lowVertices q G)
    (hOutside : ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1) :
    (lowVertices q G).card + (∑ t ∈ P, (signedDeficiency q G t - 1)) = ∑ v, positiveDeficiency q G v := by
  have hSplit := Finset.sum_sdiff (f := signedDeficiency q G) hLow
  have hX : (∑ v ∈ lowVertices q G \ P, signedDeficiency q G v) = ((lowVertices q G \ P).card : ℤ) := by
    rw [Finset.sum_congr rfl hOutside]
    simp
  have hTau : (∑ t ∈ P, (signedDeficiency q G t - 1)) = (∑ t ∈ P, signedDeficiency q G t) - P.card := by
    simp [Finset.sum_sub_distrib]
  have hCard : ((lowVertices q G \ P).card : ℤ) + P.card = (lowVertices q G).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hLow
  rw [hX, lowVertices_signed_sum] at hSplit
  linarith

/-- Low points covered by a packing split into the paired rows and the covered outside lows. -/
theorem open_packing_low_incidence_identity {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) :
    (packingCovered G P ∩ lowVertices q G).card =
      (pairedPackingRows G P).card + (packingCovered G P ∩ (lowVertices q G \ P)).card := by
  have hPoint (t : Fin n) : (G.neighborFinset t ∩ (lowVertices q G \ P)).card +
      (G.neighborFinset t ∩ P).card = (G.neighborFinset t ∩ lowVertices q G).card := by
    have h := Finset.card_sdiff_add_card_inter (G.neighborFinset t ∩ lowVertices q G) P
    have hDiff : (G.neighborFinset t ∩ lowVertices q G) \ P = G.neighborFinset t ∩ (lowVertices q G \ P) := by
      ext v
      simp [and_assoc]
    have hInter : (G.neighborFinset t ∩ lowVertices q G) ∩ P = G.neighborFinset t ∩ P := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hLow]
    rwa [hDiff, hInter] at h
  have hSum := Finset.sum_congr rfl (fun t (_ : t ∈ P) => hPoint t)
  rw [Finset.sum_add_distrib, open_packing_covered_intersection_card G P (lowVertices q G \ P) hOpen,
    open_packing_internal_degree_sum G P hOpen, open_packing_covered_intersection_card G P (lowVertices q G) hOpen] at hSum
  omega

/-- The exact hole formula at packing size q retains deep rows, paired rows, and outside low incidences. -/
theorem full_packing_holes_identity (q a : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q)
    (hOutside : ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1) :
    ((packingHoles q G P).card : ℤ) = 2 * a + 2 * (∑ t ∈ P, (signedDeficiency q G t - 1)) +
      (pairedPackingRows G P).card + (packingCovered G P ∩ (lowVertices q G \ P)).card - q - (highVertices q G).card := by
  have hHole := packing_holes_card_identity q G P hOpen
  have hLowWeight := full_packing_low_card_add_excess q G P hLow hOutside
  rw [total_positiveDeficiency_eq_signed_add_high q G hDegree, hTotal] at hLowWeight
  have hIncidence := open_packing_low_incidence_identity q G P hLow hOpen
  rw [hIncidence, hCard] at hHole
  push_cast at hHole
  nlinarith



/-- Away from the replaced vertex, the square-degree change is a binary edge update. -/
theorem parentReplacement_degree_square_change {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) (x : Fin n) (hx : x ≠ v) :
    ((parentReplacement G v T).degree x : ℤ) ^ 2 - (G.degree x : ℤ) ^ 2 =
      (if x ∈ T then 2 * (G.degree x : ℤ) + 1 else 0) +
      (if G.Adj x v then -2 * (G.degree x : ℤ) + 1 else 0) -
      2 * (if x ∈ T ∧ G.Adj x v then (1 : ℤ) else 0) := by
  have hBalance : ((parentReplacement G v T).degree x : ℤ) + (if G.Adj x v then 1 else 0) =
      (G.degree x : ℤ) + (if x ∈ T then 1 else 0) := by
    exact_mod_cast parentReplacement_degree_balance G v T x hx
  by_cases ht : x ∈ T <;> by_cases ha : G.Adj x v <;>
    simp only [ht, ha, and_self, and_false, false_and, ite_true, ite_false] at hBalance ⊢ <;>
    nlinarith

/-- A degree-preserving parent replacement has an exact global square-degree change. -/
theorem parentReplacement_degree_square_sum_change {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) (hNeutral : (T.erase v).card = G.degree v) :
    (∑ x, ((parentReplacement G v T).degree x : ℤ) ^ 2) - (∑ x, (G.degree x : ℤ) ^ 2) =
      2 * ((∑ x ∈ T.erase v, (G.degree x : ℤ)) - (∑ x ∈ G.neighborFinset v, (G.degree x : ℤ)) +
        G.degree v - (G.neighborFinset v ∩ T.erase v).card) := by
  let U : Finset (Fin n) := Finset.univ.erase v
  let H := parentReplacement G v T
  have hSelectedSet : U.filter (fun x => x ∈ T) = T.erase v := by ext x; simp [U, and_comm]
  have hAdjacentSet : U.filter (fun x => G.Adj x v) = G.neighborFinset v := by
    ext x
    constructor
    · intro hx
      exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2.symm
    · intro hx
      have hAdj := (G.mem_neighborFinset v x).mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hAdj.ne.symm, Finset.mem_univ _⟩, hAdj.symm⟩
  have hCommonSet : U.filter (fun x => x ∈ T ∧ G.Adj x v) = G.neighborFinset v ∩ T.erase v := by
    ext x
    simp only [U, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hx, hxT, hAdj⟩
      exact ⟨hAdj.symm, hx, hxT⟩
    · rintro ⟨hAdj, hx, hxT⟩
      exact ⟨hx, hxT, hAdj.symm⟩
  have hSelected : (∑ x ∈ U, if x ∈ T then 2 * (G.degree x : ℤ) + 1 else 0) =
      2 * (∑ x ∈ T.erase v, (G.degree x : ℤ)) + G.degree v := by
    rw [← Finset.sum_filter, hSelectedSet]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one, hNeutral]
  have hAdjacent : (∑ x ∈ U, if G.Adj x v then -2 * (G.degree x : ℤ) + 1 else 0) =
      -2 * (∑ x ∈ G.neighborFinset v, (G.degree x : ℤ)) + G.degree v := by
    rw [← Finset.sum_filter, hAdjacentSet]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      mul_one, SimpleGraph.card_neighborFinset_eq_degree]
  have hCommon : (∑ x ∈ U, if x ∈ T ∧ G.Adj x v then (1 : ℤ) else 0) =
      (G.neighborFinset v ∩ T.erase v).card := by
    rw [← Finset.sum_filter, hCommonSet]
    simp
  have hAway := Finset.sum_congr rfl (fun x (hx : x ∈ U) =>
    parentReplacement_degree_square_change G v T x (Finset.mem_erase.mp hx).1)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hSelected, hAdjacent, hCommon] at hAway
  have hRoot : H.degree v = G.degree v := (parentReplacement_degree_root G v T).trans hNeutral
  have hSplit := Finset.sum_erase_add Finset.univ (fun x => (H.degree x : ℤ) ^ 2 - (G.degree x : ℤ) ^ 2) (Finset.mem_univ v)
  rw [hRoot, sub_self, add_zero] at hSplit
  simp only [Finset.sum_sub_distrib] at hSplit
  change (∑ x ∈ U, (H.degree x : ℤ) ^ 2) - (∑ x ∈ U, (G.degree x : ℤ) ^ 2) = _ at hSplit
  change _ = 2 * (_ - _ + _ - _)
  change (∑ x ∈ U, (H.degree x : ℤ) ^ 2) - (∑ x ∈ U, (G.degree x : ℤ) ^ 2) = _ at hAway
  linarith

/-- The same square-degree change is expressed by neighboring signed deficiency. -/
theorem parentReplacement_degree_square_sum_deficiency {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) (hNeutral : (T.erase v).card = G.degree v) :
    (∑ x, ((parentReplacement G v T).degree x : ℤ) ^ 2) - (∑ x, (G.degree x : ℤ) ^ 2) =
      2 * ((∑ x ∈ G.neighborFinset v, signedDeficiency q G x) -
        (∑ x ∈ T.erase v, signedDeficiency q G x) + G.degree v - (G.neighborFinset v ∩ T.erase v).card) := by
  have hNew : (∑ x ∈ T.erase v, signedDeficiency q G x) =
      ((q : ℤ) + 1) * G.degree v - ∑ x ∈ T.erase v, (G.degree x : ℤ) := by
    simp [signedDeficiency, Finset.sum_sub_distrib, hNeutral, mul_comm]
  have hOld : (∑ x ∈ G.neighborFinset v, signedDeficiency q G x) =
      ((q : ℤ) + 1) * G.degree v - ∑ x ∈ G.neighborFinset v, (G.degree x : ℤ) := by
    simp [signedDeficiency, Finset.sum_sub_distrib, SimpleGraph.card_neighborFinset_eq_degree, mul_comm]
  have h := parentReplacement_degree_square_sum_change G v T hNeutral
  linarith


/-- Twice the number of triangles through a vertex, expressed by common-neighbor counts. -/
def triangleTwice {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  ∑ w ∈ G.neighborFinset v, codegree G v w

/-- The number of oriented closed three-edge walks. -/
def triangleWalkTotal {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := ∑ v, triangleTwice G v

/-- A cyclic triple sum splits into the part avoiding v and three equal incident parts. -/
theorem cyclic_triple_sum_split {n : ℕ} (f : Fin n → Fin n → Fin n → ℤ) (v : Fin n)
    (hCycle : ∀ x y z, f x y z = f y z x)
    (hFirst : ∀ x, f v v x = 0) (hMiddle : ∀ x, f v x v = 0) (hLast : ∀ x, f x v v = 0) :
    (∑ x, ∑ y, ∑ z, f x y z) =
      (∑ x ∈ Finset.univ.erase v, ∑ y ∈ Finset.univ.erase v, ∑ z ∈ Finset.univ.erase v, f x y z) +
        3 * (∑ y, ∑ z, f v y z) := by
  let U : Finset (Fin n) := Finset.univ.erase v
  have hOne (g : Fin n → ℤ) : (∑ x, g x) = (∑ x ∈ U, g x) + g v := by
    exact (Finset.sum_erase_add Finset.univ g (Finset.mem_univ v)).symm
  have hExpand : (∑ x, ∑ y, ∑ z, f x y z) =
      (∑ x ∈ U, ∑ y ∈ U, ∑ z ∈ U, f x y z) +
      (∑ x ∈ U, ∑ y ∈ U, f x y v) +
      (∑ x ∈ U, ∑ z ∈ U, f x v z) +
      (∑ y ∈ U, ∑ z ∈ U, f v y z) := by
    simp only [hOne, Finset.sum_add_distrib, hFirst, hMiddle, hLast,
      Finset.sum_const_zero, add_zero]
  have hSecond : (∑ x ∈ U, ∑ y ∈ U, f x y v) = ∑ x ∈ U, ∑ y ∈ U, f v x y := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact (hCycle x y v).trans (hCycle y v x)
  have hThird : (∑ x ∈ U, ∑ z ∈ U, f x v z) = ∑ y ∈ U, ∑ z ∈ U, f v y z := by
    calc
      _ = ∑ x ∈ U, ∑ z ∈ U, f v z x := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro z _
        exact hCycle x v z
      _ = _ := Finset.sum_comm
  have hRoot : (∑ y, ∑ z, f v y z) = ∑ y ∈ U, ∑ z ∈ U, f v y z := by
    simp only [hOne, hFirst, hMiddle, Finset.sum_const_zero, add_zero]
  rw [hExpand, hSecond, hThird, hRoot]
  ring

/-- The local triangle count is the diagonal of the cubed adjacency matrix. -/
theorem triangleTwice_eq_cube_diagonal {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (triangleTwice G v : ℤ) = (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) v v := by
  rw [Matrix.mul_assoc, G.adjMatrix_mul_apply]
  simp_rw [adjMatrix_square_codegree, codegree_symm G]
  simp only [triangleTwice, Nat.cast_sum]

/-- The local triangle count has its direct ordered triple-sum form. -/
theorem triangleTwice_eq_triple_sum {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (triangleTwice G v : ℤ) = ∑ y, ∑ z, G.adjMatrix ℤ v y * G.adjMatrix ℤ y z * G.adjMatrix ℤ z v := by
  rw [triangleTwice_eq_cube_diagonal, Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- Split the triangle-walk total into triples avoiding v and triples through v. -/
theorem triangleWalkTotal_split {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (triangleWalkTotal G : ℤ) =
      (∑ x ∈ Finset.univ.erase v, ∑ y ∈ Finset.univ.erase v, ∑ z ∈ Finset.univ.erase v,
        G.adjMatrix ℤ x y * G.adjMatrix ℤ y z * G.adjMatrix ℤ z x) + 3 * triangleTwice G v := by
  let f := fun x y z => G.adjMatrix ℤ x y * G.adjMatrix ℤ y z * G.adjMatrix ℤ z x
  have hCycle : ∀ x y z, f x y z = f y z x := by intros; dsimp only [f]; ring
  have hFirst : ∀ x, f v v x = 0 := by intro x; simp [f]
  have hMiddle : ∀ x, f v x v = 0 := by intro x; simp [f]
  have hLast : ∀ x, f x v v = 0 := by intro x; simp [f]
  have h := cyclic_triple_sum_split f v hCycle hFirst hMiddle hLast
  have hTotal : (triangleWalkTotal G : ℤ) = ∑ x, ∑ y, ∑ z, f x y z := by
    simp only [triangleWalkTotal, Nat.cast_sum, triangleTwice_eq_triple_sum]
    rfl
  rw [hTotal, h]
  rw [triangleTwice_eq_triple_sum]

/-- Replacing one neighborhood changes the total triangle count only through that vertex. -/
theorem parentReplacement_triangleWalkTotal_change {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) :
    (triangleWalkTotal (parentReplacement G v T) : ℤ) - triangleWalkTotal G =
      3 * ((triangleTwice (parentReplacement G v T) v : ℤ) - triangleTwice G v) := by
  let H := parentReplacement G v T
  let U : Finset (Fin n) := Finset.univ.erase v
  have hEntry (x) (hx : x ∈ U) (y) (hy : y ∈ U) : H.adjMatrix ℤ x y = G.adjMatrix ℤ x y := by
    have hxv := (Finset.mem_erase.mp hx).1
    have hyv := (Finset.mem_erase.mp hy).1
    simp only [H, SimpleGraph.adjMatrix_apply, parentReplacement_away_adj G v T x y hxv hyv]
  have hAvoid : (∑ x ∈ U, ∑ y ∈ U, ∑ z ∈ U, H.adjMatrix ℤ x y * H.adjMatrix ℤ y z * H.adjMatrix ℤ z x) =
      ∑ x ∈ U, ∑ y ∈ U, ∑ z ∈ U, G.adjMatrix ℤ x y * G.adjMatrix ℤ y z * G.adjMatrix ℤ z x := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    rw [hEntry x hx y hy, hEntry y hy z hz, hEntry z hz x hx]
  have hOld := triangleWalkTotal_split G v
  have hNew := triangleWalkTotal_split H v
  change (triangleWalkTotal G : ℤ) = (∑ x ∈ U, ∑ y ∈ U, ∑ z ∈ U, _) + _ at hOld
  change (triangleWalkTotal H : ℤ) = (∑ x ∈ U, ∑ y ∈ U, ∑ z ∈ U, _) + _ at hNew
  rw [hAvoid] at hNew
  linarith

/-- The replacement vertex's triangles are the edges induced by its selected neighborhood. -/
theorem parentReplacement_triangleTwice_root {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) :
    triangleTwice (parentReplacement G v T) v = ∑ x ∈ T.erase v, (G.neighborFinset x ∩ T.erase v).card := by
  rw [triangleTwice, parentReplacement_neighbor_root]
  apply Finset.sum_congr rfl
  intro x hx
  unfold codegree
  rw [parentReplacement_neighbor_root]
  have hxv := (Finset.mem_erase.mp hx).1
  congr 1
  ext y
  constructor
  · intro hy
    obtain ⟨hyS, hyH⟩ := Finset.mem_inter.mp hy
    have hyv := (Finset.mem_erase.mp hyS).1
    have hAdj := ((parentReplacement G v T).mem_neighborFinset x y).mp hyH
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr
      ((parentReplacement_away_adj G v T x y hxv hyv).mp hAdj), hyS⟩
  · intro hy
    obtain ⟨hyG, hyS⟩ := Finset.mem_inter.mp hy
    have hyv := (Finset.mem_erase.mp hyS).1
    have hAdj := (G.mem_neighborFinset x y).mp hyG
    exact Finset.mem_inter.mpr ⟨hyS, ((parentReplacement G v T).mem_neighborFinset x y).mpr
      ((parentReplacement_away_adj G v T x y hxv hyv).mpr hAdj)⟩


/-- An integral degree-and-triangle objective for choosing an edge extremizer. -/
def triangleWeightedObjective {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  3 * (∑ v, G.degree v ^ 2) + triangleWalkTotal G

/-- The degree-and-triangle objective changes by the exact local parent formula. -/
theorem parentReplacement_objective_change {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) (hNeutral : (T.erase v).card = G.degree v) :
    (triangleWeightedObjective (parentReplacement G v T) : ℤ) - triangleWeightedObjective G =
      3 * (2 * ((∑ x ∈ G.neighborFinset v, signedDeficiency q G x) -
        (∑ x ∈ T.erase v, signedDeficiency q G x) + G.degree v - (G.neighborFinset v ∩ T.erase v).card) +
        (∑ x ∈ T.erase v, (G.neighborFinset x ∩ T.erase v).card : ℕ) - triangleTwice G v) := by
  have hSquares := parentReplacement_degree_square_sum_deficiency q G v T hNeutral
  have hTriangles := parentReplacement_triangleWalkTotal_change G v T
  rw [parentReplacement_triangleTwice_root] at hTriangles
  simp only [triangleWeightedObjective, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  push_cast at hTriangles
  linarith

/-- Objective minimality yields the local parent exchange inequality. -/
theorem minimizing_parent_exchange {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G)
    (hMinimal : ∀ H : SimpleGraph (Fin n), (cycleGraph 4).Free H → H.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective H)
    (v : Fin n) (T : Finset (Fin n))
    (hOpen : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → codegree G x y = 0)
    (hNeutral : (T.erase v).card = G.degree v) :
    2 * (∑ x ∈ T.erase v, signedDeficiency q G x) + triangleTwice G v +
      2 * (G.neighborFinset v ∩ T.erase v).card ≤
        2 * (∑ x ∈ G.neighborFinset v, signedDeficiency q G x) + 2 * (G.degree v : ℤ) +
          (∑ x ∈ T.erase v, (G.neighborFinset x ∩ T.erase v).card : ℕ) := by
  have hCount := parentReplacement_edge_count G v T
  rw [hNeutral] at hCount
  have hEdges : (parentReplacement G v T).edgeFinset.card = G.edgeFinset.card := by omega
  have hMin := hMinimal (parentReplacement G v T) (parentReplacement_free G hFree v T hOpen) hEdges
  have hMinInt : (triangleWeightedObjective G : ℤ) ≤ triangleWeightedObjective (parentReplacement G v T) := by
    exact_mod_cast hMin
  have hChange := parentReplacement_objective_change q G v T hNeutral
  linarith

/-- Removing a selected vertex deletes one incidence at each selected neighbor. -/
theorem neighbor_intersection_erase_balance {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (v x : Fin n) (hv : v ∈ P) :
    (G.neighborFinset x ∩ P.erase v).card + (if G.Adj x v then 1 else 0) = (G.neighborFinset x ∩ P).card := by
  have hSet : G.neighborFinset x ∩ P.erase v = (G.neighborFinset x ∩ P).erase v := by ext y; simp [and_left_comm]
  rw [hSet]
  by_cases hAdj : G.Adj x v
  · rw [ite_eq_left hAdj]
    exact Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x v).mpr hAdj, hv⟩)
  · rw [ite_eq_right hAdj, add_zero]
    have hNot : v ∉ G.neighborFinset x ∩ P := fun h => hAdj ((G.mem_neighborFinset x v).mp (Finset.mem_inter.mp h).1)
    rw [Finset.erase_eq_of_notMem hNot]

/-- Removing a selected vertex deletes both orientations of each incident edge. -/
theorem internal_degree_sum_erase {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (v : Fin n) (hv : v ∈ P) :
    (∑ x ∈ P.erase v, (G.neighborFinset x ∩ P.erase v).card) +
      2 * (G.neighborFinset v ∩ P).card = ∑ x ∈ P, (G.neighborFinset x ∩ P).card := by
  have hBalance := Finset.sum_congr rfl (fun x (_ : x ∈ P.erase v) => neighbor_intersection_erase_balance G P v x hv)
  rw [Finset.sum_add_distrib] at hBalance
  have hAdjacent : (∑ x ∈ P.erase v, if G.Adj x v then 1 else 0) = (G.neighborFinset v ∩ P).card := by
    rw [← Finset.sum_filter]
    have hSet : (P.erase v).filter (fun x => G.Adj x v) = G.neighborFinset v ∩ P := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxP, hxAdj⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v x).mpr hxAdj.symm, (Finset.mem_erase.mp hxP).2⟩
      · intro hx
        obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
        have hAdj := (G.mem_neighborFinset v x).mp hxN
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hAdj.ne.symm, hxP⟩, hAdj.symm⟩
    simp [hSet]
  rw [hAdjacent] at hBalance
  have hSplit := Finset.sum_erase_add P (fun x => (G.neighborFinset x ∩ P).card) hv
  omega

/-- An outside unit low satisfies the doubled version of the manuscript's exchange inequality. -/
theorem minimizing_outside_unit_exchange (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hMinimal : ∀ H : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free H → H.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective H)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hCard : P.card = q)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∉ P) (hUnit : signedDeficiency q G v = 1) :
    2 * (∑ t ∈ P, (signedDeficiency q G t - 1)) + triangleTwice G v ≤
      2 * (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) -
        2 * (G.neighborFinset v ∩ P).card + (pairedPackingRows G P).card := by
  have hDegree : G.degree v = q := by unfold signedDeficiency at hUnit; omega
  have hNeutral : (P.erase v).card = G.degree v := by rw [Finset.erase_eq_of_notMem hv, hCard, hDegree]
  have hParent := minimizing_parent_exchange q G hFree hMinimal v P hOpen hNeutral
  rw [Finset.erase_eq_of_notMem hv, hDegree, open_packing_internal_degree_sum G P hOpen] at hParent
  have hExcess : (∑ t ∈ P, (signedDeficiency q G t - 1)) = (∑ t ∈ P, signedDeficiency q G t) - q := by
    simp [Finset.sum_sub_distrib, hCard]
  linarith

/-- A deep packing row satisfies the doubled inside exchange inequality. -/
theorem minimizing_deep_packing_exchange (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hMinimal : ∀ H : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free H → H.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective H)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hCard : P.card = q)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (v : Fin (q ^ 2 + q + 2)) (hv : v ∈ P) (hDeep : signedDeficiency q G v = 2) :
    2 * (∑ t ∈ P, (signedDeficiency q G t - 1)) + triangleTwice G v ≤
      2 + 2 * (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) -
        4 * (G.neighborFinset v ∩ P).card + (pairedPackingRows G P).card := by
  have hDegree : G.degree v + 1 = q := by unfold signedDeficiency at hDeep; omega
  have hErase := Finset.card_erase_add_one hv
  have hNeutral : (P.erase v).card = G.degree v := by omega
  have hParent := minimizing_parent_exchange q G hFree hMinimal v P hOpen hNeutral
  have hInter : G.neighborFinset v ∩ P.erase v = G.neighborFinset v ∩ P := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_erase.mp (Finset.mem_inter.mp hx).2).2⟩
    · intro hx
      obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
      have hAdj := (G.mem_neighborFinset v x).mp hxN
      exact Finset.mem_inter.mpr ⟨hxN, Finset.mem_erase.mpr ⟨hAdj.ne.symm, hxP⟩⟩
  rw [hInter] at hParent
  have hInternal := internal_degree_sum_erase G P v hv
  rw [open_packing_internal_degree_sum G P hOpen] at hInternal
  have hInternalInt : (∑ x ∈ P.erase v, ((G.neighborFinset x ∩ P.erase v).card : ℤ)) +
      2 * (G.neighborFinset v ∩ P).card = (pairedPackingRows G P).card := by exact_mod_cast hInternal
  have hSum := Finset.sum_erase_add P (signedDeficiency q G) hv
  rw [hDeep] at hSum
  have hExcess : (∑ t ∈ P, (signedDeficiency q G t - 1)) = (∑ t ∈ P, signedDeficiency q G t) - q := by
    simp [Finset.sum_sub_distrib, hCard]
  have hDegreeInt : (G.degree v : ℤ) + 1 = q := by exact_mod_cast hDegree
  push_cast at hParent
  linarith


/-- A family inside one neighborhood has at most one incidence from each exterior point. -/
theorem neighborhood_family_covered_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (t : Fin n) (Y E : Finset (Fin n))
    (hY : Y ⊆ G.neighborFinset t) (ht : t ∉ E)
    (hCover : ∀ y ∈ Y, ∃ z ∈ E, G.Adj y z) : Y.card ≤ E.card := by
  have hLower : Y.card ≤ ∑ y ∈ Y, (G.neighborFinset y ∩ E).card := by
    calc
      _ = ∑ _y ∈ Y, 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨z, hz, hyz⟩ := hCover y hy
        exact Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y z).mpr hyz, hz⟩⟩
  rw [sum_neighbor_intersection_card G Y E] at hLower
  have hUpper : (∑ z ∈ E, (G.neighborFinset z ∩ Y).card) ≤ E.card := by
    calc
      _ ≤ ∑ _z ∈ E, 1 := by
        apply Finset.sum_le_sum
        intro z hz
        have hNe : z ≠ t := fun h => ht (h ▸ hz)
        have hSubset : G.neighborFinset z ∩ Y ⊆ G.neighborFinset z ∩ G.neighborFinset t :=
          fun _ h => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1, hY (Finset.mem_inter.mp h).2⟩
        exact (Finset.card_le_card hSubset).trans (codegree_le_one G hFree z t hNe)
      _ = _ := by simp
  omega

/-- The exterior of a full packing and all its neighborhoods has the stated exact size. -/
theorem full_packing_exterior_card (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (P : Finset (Fin (q ^ 2 + q + 2)))
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q) :
    ((Finset.univ \ (P ∪ packingCovered G P)).card : ℤ) =
      2 + (∑ t ∈ P, (signedDeficiency q G t - 1)) + (pairedPackingRows G P).card := by
  have hInter : P ∩ packingCovered G P = pairedPackingRows G P := by
    ext t
    simp only [Finset.mem_inter, packingCovered, pairedPackingRows, Finset.mem_filter, Finset.mem_univ, true_and]
  have hUnion : ((P ∪ packingCovered G P).card : ℤ) + (pairedPackingRows G P).card =
      P.card + (packingCovered G P).card := by
    have h := Finset.card_union_add_card_inter P (packingCovered G P)
    rw [hInter] at h
    exact_mod_cast h
  have hExterior : ((Finset.univ \ (P ∪ packingCovered G P)).card : ℤ) + (P ∪ packingCovered G P).card =
      (q : ℤ) ^ 2 + q + 2 := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (q ^ 2 + q + 2))) (P ∪ packingCovered G P)
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have hCovered := open_packing_covered_card_by_excess q G P hOpen
  rw [hCard] at hCovered hUnion
  nlinarith

/-- Each nonlow neighbor of a paired row has a neighbor outside the packing and its neighborhoods. -/
theorem paired_nonlow_has_exterior_neighbor (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q)
    (t : Fin (q ^ 2 + q + 2)) (ht : t ∈ pairedPackingRows G P)
    (x : Fin (q ^ 2 + q + 2)) (hx : x ∈ G.neighborFinset t \ lowVertices q G) :
    ∃ z ∈ Finset.univ \ (P ∪ packingCovered G P), G.Adj x z := by
  obtain ⟨htP, htNeighbor⟩ := Finset.mem_filter.mp ht
  have htCovered : t ∈ packingCovered G P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, htNeighbor⟩
  obtain ⟨hxN, hxNotLow⟩ := Finset.mem_sdiff.mp hx
  have htx := (G.mem_neighborFinset t x).mp hxN
  have hxNotP : x ∉ P := fun h => hxNotLow (hLow h)
  have hxDegree : q + 1 ≤ G.degree x := by
    have hNonpositive : signedDeficiency q G x ≤ 0 := by
      by_contra h
      exact hxNotLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
    unfold signedDeficiency at hNonpositive
    omega
  have hUnique := Finset.card_le_one.mp (open_packing_neighbor_card_le_one G P hOpen x)
  have hPNeighbors : G.neighborFinset x ∩ P ⊆ packingCovered G P := by
    intro y hy
    have htX : t ∈ G.neighborFinset x ∩ P := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x t).mpr htx.symm, htP⟩
    have hEq : y = t := hUnique y hy t htX
    exact hEq.symm ▸ htCovered
  have hSet : G.neighborFinset x ∩ (P ∪ packingCovered G P) = G.neighborFinset x ∩ packingCovered G P := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyN, hyPU⟩ := Finset.mem_inter.mp hy
      rcases Finset.mem_union.mp hyPU with hyP | hyU
      · exact Finset.mem_inter.mpr ⟨hyN, hPNeighbors (Finset.mem_inter.mpr ⟨hyN, hyP⟩)⟩
      · exact Finset.mem_inter.mpr ⟨hyN, hyU⟩
    · intro hy
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).1, Finset.mem_union_right _ (Finset.mem_inter.mp hy).2⟩
  have hCovered := open_packing_covered_neighbors_outside G hFree P hOpen x hxNotP
  rw [hCard] at hCovered
  have hInside : (G.neighborFinset x ∩ packingCovered G P).card ≤ q := by
    exact_mod_cast (show ((G.neighborFinset x ∩ packingCovered G P).card : ℤ) ≤ q by omega)
  have hPartition := Finset.card_sdiff_add_card_inter (G.neighborFinset x) (P ∪ packingCovered G P)
  rw [hSet, SimpleGraph.card_neighborFinset_eq_degree] at hPartition
  have hPositive : 0 < (G.neighborFinset x \ (P ∪ packingCovered G P)).card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hPositive
  obtain ⟨hzN, hzNot⟩ := Finset.mem_sdiff.mp hz
  exact ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzNot⟩, (G.mem_neighborFinset x z).mp hzN⟩

/-- The nonlow portion of each paired row fits into the common exterior set. -/
theorem paired_nonlow_row_card_le_exterior (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q)
    (t : Fin (q ^ 2 + q + 2)) (ht : t ∈ pairedPackingRows G P) :
    (G.neighborFinset t \ lowVertices q G).card ≤ (Finset.univ \ (P ∪ packingCovered G P)).card := by
  apply neighborhood_family_covered_card_le G hFree t
    (G.neighborFinset t \ lowVertices q G) (Finset.univ \ (P ∪ packingCovered G P)) Finset.sdiff_subset
  · intro h
    have htP := (Finset.mem_filter.mp ht).1
    exact (Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ htP)
  · exact paired_nonlow_has_exterior_neighbor q G hFree P hLow hOpen hCard t ht

/-- At a paired row, its other low neighbors belong to the outside low set. -/
theorem paired_row_nonlow_lower (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2)))
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hDegree : ∀ t ∈ P, q ≤ G.degree t + 1)
    (t : Fin (q ^ 2 + q + 2)) (ht : t ∈ pairedPackingRows G P) :
    q ≤ (G.neighborFinset t \ lowVertices q G).card + (G.neighborFinset t ∩ (lowVertices q G \ P)).card + 2 := by
  obtain ⟨htP, htNonempty⟩ := Finset.mem_filter.mp ht
  have hOne : (G.neighborFinset t ∩ P).card = 1 := by
    have hPos := Finset.card_pos.mpr htNonempty
    have hUpper := open_packing_neighbor_card_le_one G P hOpen t
    omega
  have hLowPartition := Finset.card_sdiff_add_card_inter (G.neighborFinset t ∩ lowVertices q G) P
  have hDiff : (G.neighborFinset t ∩ lowVertices q G) \ P = G.neighborFinset t ∩ (lowVertices q G \ P) := by
    ext x
    simp [and_assoc]
  have hInter : (G.neighborFinset t ∩ lowVertices q G) ∩ P = G.neighborFinset t ∩ P := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hLow]
  rw [hDiff, hInter, hOne] at hLowPartition
  have hPartition := Finset.card_sdiff_add_card_inter (G.neighborFinset t) (lowVertices q G)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hPartition
  have hMin := hDegree t htP
  omega

/-- The paired-row incidence inequality in the full-packing branch. -/
theorem paired_rows_incidence_bound (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q)
    (hDegree : ∀ t ∈ P, q ≤ G.degree t + 1) :
    ((pairedPackingRows G P).card : ℤ) * ((q : ℤ) - 4 - (∑ t ∈ P, (signedDeficiency q G t - 1)) -
      (pairedPackingRows G P).card) ≤ (lowVertices q G \ P).card := by
  have hExterior := full_packing_exterior_card q G P hOpen hCard
  have hEach (t) (ht : t ∈ pairedPackingRows G P) :
      (q : ℤ) - 4 - (∑ t ∈ P, (signedDeficiency q G t - 1)) - (pairedPackingRows G P).card ≤
        (G.neighborFinset t ∩ (lowVertices q G \ P)).card := by
    have hLower : (q : ℤ) ≤ (G.neighborFinset t \ lowVertices q G).card +
        (G.neighborFinset t ∩ (lowVertices q G \ P)).card + 2 := by
      exact_mod_cast paired_row_nonlow_lower q G P hLow hOpen hDegree t ht
    have hUpper : ((G.neighborFinset t \ lowVertices q G).card : ℤ) ≤ (Finset.univ \ (P ∪ packingCovered G P)).card := by
      exact_mod_cast paired_nonlow_row_card_le_exterior q G hFree P hLow hOpen hCard t ht
    linarith
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  have hIncidence : (∑ t ∈ pairedPackingRows G P, ((G.neighborFinset t ∩ (lowVertices q G \ P)).card : ℤ)) ≤
      (lowVertices q G \ P).card := by
    calc
      _ ≤ ∑ t ∈ P, ((G.neighborFinset t ∩ (lowVertices q G \ P)).card : ℤ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Int.natCast_nonneg _)
      _ = ((packingCovered G P ∩ (lowVertices q G \ P)).card : ℤ) := by
        exact_mod_cast open_packing_covered_intersection_card G P (lowVertices q G \ P) hOpen
      _ ≤ _ := by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : packingCovered G P ∩ (lowVertices q G \ P) ⊆ lowVertices q G \ P)
  exact hSum.trans hIncidence


/-- A unit low adjacent to a low row covers that row's untriangulated regular neighbors. -/
theorem adjacent_unit_from_low_positive_cover {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l w v : Fin n)
    (hLW : G.Adj l w) (hLV : G.Adj l v)
    (hW : signedDeficiency q G w = 1) (hV : signedDeficiency q G v = 0)
    (hUntri : codegree G l v = 0) :
    ∃ z ∈ G.neighborFinset v, z ∈ positivePartners q G w := by
  have hWV : w ≠ v := by intro h; subst v; omega
  have hNotWV : ¬G.Adj w v := by
    intro h
    exact (codegree_eq_zero_iff G l v).mp hUntri w hLW h.symm
  have hCommon : 0 < codegree G w v := by
    apply Finset.card_pos.mpr
    exact ⟨l, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w l).mpr hLW.symm,
      (G.mem_neighborFinset v l).mpr hLV.symm⟩⟩
  have hCodegree : codegree G w v = 1 := by
    have h := codegree_le_one G hFree w v hWV
    omega
  have hZWV : weightedResidual q G w v = 0 := by
    rw [weightedResidual_nonadj q G w v hWV hNotWV, hCodegree]
    norm_num
  have hZLV : weightedResidual q G l v = 1 - signedDeficiency q G l := by
    rw [weightedResidual_off_diagonal q G l v hLV.ne, adjMatrix_square_codegree]
    simp only [G.adjMatrix_apply, ite_eq_left hLV, hUntri, hV, Nat.cast_zero, sub_zero, add_zero, one_mul]
  have hZWL : weightedResidual q G w l ≤ -signedDeficiency q G l := by
    rw [weightedResidual_off_diagonal q G w l hLW.symm.ne, adjMatrix_square_codegree]
    simp only [G.adjMatrix_apply, ite_eq_left hLW.symm, hW, one_mul]
    have hNonneg : (0 : ℤ) ≤ codegree G w l := Int.natCast_nonneg _
    omega
  have hLNW : l ∈ G.neighborFinset w := (G.mem_neighborFinset w l).mpr hLW.symm
  have hLNV : l ∈ G.neighborFinset v := (G.mem_neighborFinset v l).mpr hLV.symm
  have hLeftRest : 0 ≤ ∑ z ∈ (G.neighborFinset w).erase l, weightedResidual q G z v := by
    apply Finset.sum_nonneg
    intro z hz
    have hZL := (Finset.mem_erase.mp hz).1
    have hWZ := (G.mem_neighborFinset w z).mp (Finset.mem_erase.mp hz).2
    have hZV : z ≠ v := by intro h; subst z; exact hNotWV hWZ
    have hNotZV : ¬G.Adj z v := by
      intro h
      have hEq := common_neighbor_unique G hFree hWV hLW.symm hLV.symm hWZ h.symm
      exact hZL hEq.symm
    exact weightedResidual_nonadj_nonnegative q G hFree z v hZV hNotZV
  have hLeft := Finset.sum_erase_add (G.neighborFinset w) (fun z => weightedResidual q G z v) hLNW
  rw [hZLV] at hLeft
  have hLeftBound : 1 - signedDeficiency q G l ≤ ∑ z ∈ G.neighborFinset w, weightedResidual q G z v := by linarith
  by_contra hNone
  push Not at hNone
  have hRightRest : (∑ z ∈ (G.neighborFinset v).erase l, weightedResidual q G w z) ≤ 0 := by
    apply Finset.sum_nonpos
    intro z hz
    have hNot := hNone z (Finset.mem_erase.mp hz).2
    have hNonpos : ¬0 < weightedResidual q G w z := by
      intro h
      exact hNot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have hRight := Finset.sum_erase_add (G.neighborFinset v) (fun z => weightedResidual q G w z) hLNV
  have hRightBound : (∑ z ∈ G.neighborFinset v, weightedResidual q G w z) ≤ -signedDeficiency q G l := by linarith
  have hComm := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M w v) (weightedAdjacency_commutes_residual q G)
  simp only [weightedAdjacency_mul_apply, mul_weightedAdjacency_apply, hW, hV, hZWV, mul_zero, add_zero] at hComm
  linarith

/-- A unit neighbor's positive row injectively covers the untriangulated regular part of any low row. -/
theorem adjacent_low_untriangulated_card_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (l w : Fin n) (hLW : G.Adj l w)
    (hL : 1 ≤ signedDeficiency q G l) (hW : signedDeficiency q G w = 1) :
    (regularNeighbors q G l).card - (triangularRegularNeighbors q G l).card ≤ (positivePartners q G w).card := by
  let U := regularNeighbors q G l \ triangularRegularNeighbors q G l
  have hCover (v) (hv : v ∈ U) : ∃ z ∈ positivePartners q G w, G.Adj z v := by
    obtain ⟨hLV, hV, hUntri⟩ := untriangulated_regular_neighbor q G hFree l v hv
    obtain ⟨z, hz, hPositive⟩ := adjacent_unit_from_low_positive_cover q G hFree l w v hLW hLV hW hV hUntri
    exact ⟨z, hPositive, ((G.mem_neighborFinset v z).mp hz).symm⟩
  let cover := fun v => if hv : v ∈ U then (hCover v hv).choose else w
  have hSpec (v) (hv : v ∈ U) : cover v ∈ positivePartners q G w ∧ G.Adj (cover v) v := by
    dsimp only [cover]
    rw [dite_eq_left hv]
    exact (hCover v hv).choose_spec
  have hNotL : l ∉ positivePartners q G w := by
    intro h
    have hPositive := (Finset.mem_filter.mp h).2
    have hEntry := weightedResidual_off_diagonal q G w l hLW.symm.ne
    rw [adjMatrix_square_codegree] at hEntry
    simp only [G.adjMatrix_apply, ite_eq_left hLW.symm, hW, one_mul] at hEntry
    have hNonneg : (0 : ℤ) ≤ codegree G w l := Int.natCast_nonneg _
    omega
  have hCount : U.card ≤ (positivePartners q G w).card := by
    apply Finset.card_le_card_of_injOn cover
    · intro v hv
      exact (hSpec v hv).1
    · intro v hv x hx hEqual
      have hLV := (untriangulated_regular_neighbor q G hFree l v hv).1
      have hLX := (untriangulated_regular_neighbor q G hFree l x hx).1
      have hCV := (hSpec v hv).2
      have hCX := (hSpec x hx).2
      rw [← hEqual] at hCX
      have hDistinct : l ≠ cover v := by intro h; exact hNotL (h ▸ (hSpec v hv).1)
      exact common_neighbor_unique G hFree hDistinct hLV hCV hLX hCX
  have hSubset : triangularRegularNeighbors q G l ⊆ regularNeighbors q G l := Finset.filter_subset _ _
  have hCard := Finset.card_sdiff_add_card_eq_card hSubset
  change U.card + (triangularRegularNeighbors q G l).card = (regularNeighbors q G l).card at hCard
  omega

/-- A sublinear paired-row count makes the quadratic deep-row bound sublinear as well. -/
theorem deep_row_fraction_bound (q k t : ℤ) (hq : 1024 ≤ q) (hk : 16 * k < q)
    (hQuadratic : 2 * t ^ 2 ≤ (2 + k) * t + 6 * q) : 8 * t < q := by
  by_contra h
  have hqt : q ≤ 8 * t := by omega
  have ht : 128 ≤ t := by omega
  have hkt : 2 * k ≤ t := by omega
  have hProduct := mul_le_mul_of_nonneg_right hkt (show 0 ≤ t by omega)
  have hUpper : 3 * t ^ 2 ≤ 100 * t := by nlinarith
  have hLower := mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ 3 * t - 101 by omega)
  nlinarith

/-- Two paired rows already violate their incidence bound once both exceptional fractions are small. -/
theorem paired_row_fraction_contradiction (q k t h x : ℤ) (hq : 64 ≤ q) (hh : 4 * h < q)
    (hk : 2 ≤ k) (hkSmall : 16 * k < q) (htSmall : 8 * t < q)
    (hIncidence : k * (q - 4 - t - k) ≤ x) (hOutside : x ≤ q + h) : False := by
  have hGap : 3 * q < 4 * (q - 4 - t - k) := by omega
  have hPositive : 0 ≤ q - 4 - t - k := by omega
  have hProduct := mul_le_mul_of_nonneg_right hk hPositive
  nlinarith


/-- The hole argument excludes a positive fixed fraction of paired packing rows. -/
theorem full_packing_paired_fraction_bound (q T K M E H a : ℕ) (hq : 1 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hPositive : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ))
    (hIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hJ : (boundedLightTriangleRegularVertices q T G).card ≤ 72) (hHigh : (highVertices q G).card ≤ H)
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0) (hCard : P.card = q)
    (hMinPacking : ∀ t ∈ P, q ≤ G.degree t + 1)
    (hOutsideUnit : ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) :
    let R : ℕ := 2 + K * M + 72 + H + M + 1
    let N : ℕ := 18 * (2 * R) ^ 2
    let C : ℕ := 4 * (2 + E) + (E + 1 + K) * N + K * N ^ 2
    6 * (2 * R) ^ 2 + C + 2 * H + 60 < a → 16 * (pairedPackingRows G P).card < q := by
  dsimp only
  intro hLarge
  let R : ℕ := 2 + K * M + 72 + H + M + 1
  let N : ℕ := 18 * (2 * R) ^ 2
  let C : ℕ := 4 * (2 + E) + (E + 1 + K) * N + K * N ^ 2
  let k : ℤ := (pairedPackingRows G P).card
  let t : ℤ := ∑ v ∈ P, (signedDeficiency q G v - 1)
  let e : ℤ := (packingCovered G P ∩ (lowVertices q G \ P)).card
  let h : ℤ := (packingHoles q G P).card
  let F : ℤ := ∑ v ∈ lowVertices q G \ P, signedDeficiency q G v
  have hLow : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  have hLarge' : 6 * (2 * R) ^ 2 + C + 2 * H + 60 < a := hLarge
  have ht : 0 ≤ t := packing_excess_nonnegative q G P hLow
  have he : 0 ≤ e := Int.natCast_nonneg _
  have hh : 0 ≤ h := Int.natCast_nonneg _
  have hH : ((highVertices q G).card : ℤ) ≤ H := by exact_mod_cast hHigh
  by_contra hPairLarge
  have hkq : (q : ℤ) ≤ 16 * k := by
    dsimp only [k]
    exact_mod_cast (show q ≤ 16 * (pairedPackingRows G P).card by omega)
  have hk : 0 < k := by
    have hqInt : (1 : ℤ) ≤ q := by exact_mod_cast hq
    omega
  have hPair : k * ((q : ℤ) - 4 - t - k) ≤ (lowVertices q G \ P).card :=
    paired_rows_incidence_bound q G hFree P hLow hOpen hCard hMinPacking
  have hX : ((lowVertices q G \ P).card : ℤ) ≤ 3 * q := by
    have hCardX : ((lowVertices q G \ P).card : ℤ) ≤ (lowVertices q G).card := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : lowVertices q G \ P ⊆ lowVertices q G)
    exact hCardX.trans ((lowVertices_card_le_positiveDeficiency q G).trans hPositive)
  have hPairBound : k * ((q : ℤ) - 4 - t - k) ≤ k * 48 := by linarith only [hPair, hX, hkq]
  have hGap : (q : ℤ) - 4 - t - k ≤ 48 := (mul_le_mul_iff_of_pos_left hk).mp hPairBound
  have hHole := full_packing_holes_identity q a G hDegree hTotal P hLow hOpen hCard hOutsideUnit
  change h = 2 * a + 2 * t + k + e - q - (highVertices q G).card at hHole
  have hLower : 2 * (a : ℤ) + e - 52 - H ≤ h := by linarith only [hHole, hGap, ht, hH]
  have hThreshold : 6 * (2 * R) ^ 2 + H + 52 < a := by omega
  have hThresholdInt : 6 * (2 * (R : ℤ)) ^ 2 + H + 52 < a := by exact_mod_cast hThreshold
  have ha : (0 : ℤ) ≤ a := Int.natCast_nonneg _
  have hCoarse : H + 52 < a := by omega
  have hCoarseInt : (H : ℤ) + 52 < a := by exact_mod_cast hCoarse
  have hOrder : 6 * (2 * R) ^ 2 ≤ (packingHoles q G P).card := by
    have hInt : 6 * (2 * (R : ℤ)) ^ 2 ≤ ((packingHoles q G P).card : ℤ) := by
      change 6 * (2 * (R : ℤ)) ^ 2 ≤ h
      linarith only [hLower, hThresholdInt, ha, he]
    exact_mod_cast hInt
  have hEta : (packingCovered G P ∩ (lowVertices q G \ P)).card ≤ 2 * (packingHoles q G P).card := by
    have hInt : ((packingCovered G P ∩ (lowVertices q G \ P)).card : ℤ) ≤ 2 * (packingHoles q G P).card := by
      change e ≤ 2 * h
      linarith only [hLower, hCoarseInt, ha, hh]
    exact_mod_cast hInt
  have hGapPacking : q + 2 ≤ P.card + 2 := by omega
  have hUpper := packing_unit_rows_hole_bound q T K M E 2 72 H G hFree hGlobal hIndependent hNonlight hJ hHigh
    P hP hOpen hGapPacking hOutside (by simpa only [R, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hOrder) hEta
  have hUpper' : ((packingUnitRows q G P).card : ℤ) ≤ F + C := by
    simpa only [F, C, N, R, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
      add_assoc, add_comm, add_left_comm] using hUpper
  have hUnit := packing_unit_rows_excess_lower q a G hDegree hTotal P hLow
  have hCardInt : (P.card : ℤ) = q := by exact_mod_cast hCard
  have hLowerUnit : F + 2 * a - 2 - H ≤ (packingUnitRows q G P).card := by
    change F + 2 * (a : ℤ) + 2 - 2 * ((q : ℤ) + 2 - P.card) - (highVertices q G).card ≤ (packingUnitRows q G P).card at hUnit
    linarith only [hUnit, hCardInt, hH]
  have hSmallA : 2 * (a : ℤ) ≤ C + H + 2 := by linarith only [hLowerUnit, hUpper']
  have hABound : C + H + 2 < a := by omega
  have hABoundInt : (C : ℤ) + H + 2 < a := by exact_mod_cast hABound
  linarith only [hSmallA, hABoundInt, ha]


/-- Summing the deep-row exchanges gives a quadratic bound for the packing excess. -/
theorem deep_rows_quadratic_bound (q : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hMinimal : ∀ H : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free H → H.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective H)
    (hPositive : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ))
    (P : Finset (Fin (q ^ 2 + q + 2))) (hCard : P.card = q)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hInside : ∀ t ∈ P, signedDeficiency q G t = 1 ∨ signedDeficiency q G t = 2) :
    2 * (∑ t ∈ P, (signedDeficiency q G t - 1)) ^ 2 ≤
      (2 + ((pairedPackingRows G P).card : ℤ)) * (∑ t ∈ P, (signedDeficiency q G t - 1)) + 6 * q := by
  let D := P.filter fun t => signedDeficiency q G t = 2
  let tau : ℤ := ∑ t ∈ P, (signedDeficiency q G t - 1)
  let c := fun v => ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w
  have hCardD : (D.card : ℤ) = tau := (full_packing_excess_eq_deep_card q G P hInside).symm
  have hOpenD : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → codegree G x y = 0 := by
    intro x hx y hy hNe
    exact hOpen x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hNe
  have hEach (v) (hv : v ∈ D) : 2 * tau ≤ 2 + (pairedPackingRows G P).card + 2 * c v := by
    obtain ⟨hvP, hvDeep⟩ := Finset.mem_filter.mp hv
    have hExchange := minimizing_deep_packing_exchange q G hFree hMinimal P hCard hOpen v hvP hvDeep
    have hWeight : (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) ≤ c v :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    have hTriangle : (0 : ℤ) ≤ triangleTwice G v := Int.natCast_nonneg _
    have hInternal : (0 : ℤ) ≤ (G.neighborFinset v ∩ P).card := Int.natCast_nonneg _
    change 2 * tau + _ ≤ _ at hExchange
    linarith only [hExchange, hWeight, hTriangle, hInternal]
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hSum
  rw [hCardD] at hSum
  have hWeightSum : (∑ v ∈ D, c v) ≤ 3 * (q : ℤ) := by
    have hCover := open_packing_covered_weight_sum G D hOpenD (positiveDeficiency q G)
    change (∑ v ∈ packingCovered G D, positiveDeficiency q G v) = ∑ v ∈ D, c v at hCover
    rw [← hCover]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => positiveDeficiency_nonnegative q G v)).trans hPositive
  change 2 * tau ^ 2 ≤ (2 + ((pairedPackingRows G P).card : ℤ)) * tau + 6 * q
  nlinarith only [hSum, hWeightSum]

/-- A minimizing full packing with a small paired fraction is independent. -/
theorem minimizing_packing_independent_of_paired_fraction (q H a : ℕ) (hq : 1024 ≤ q)
    (hHighOrder : 4 * H < q) (ha : 1 ≤ a)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hHigh : (highVertices q G).card ≤ H)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (hPositive : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ))
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G) (hCard : P.card = q)
    (hOpen : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → codegree G x y = 0)
    (hInside : ∀ t ∈ P, signedDeficiency q G t = 1 ∨ signedDeficiency q G t = 2)
    (hOutsideUnit : ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1)
    (hPaired : 16 * (pairedPackingRows G P).card < q) :
    (∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w) ∧ 8 * (∑ t ∈ P, (signedDeficiency q G t - 1)) < q := by
  let tau : ℤ := ∑ t ∈ P, (signedDeficiency q G t - 1)
  let k : ℤ := (pairedPackingRows G P).card
  have hqInt : (1024 : ℤ) ≤ q := by exact_mod_cast hq
  have hkSmall : 16 * k < q := by dsimp only [k]; exact_mod_cast hPaired
  have hQuadratic := deep_rows_quadratic_bound q G hFree hMinimal hPositive P hCard hOpen hInside
  have htSmall : 8 * tau < q := deep_row_fraction_bound (q : ℤ) k tau hqInt hkSmall hQuadratic
  have htNonnegative : 0 ≤ tau := packing_excess_nonnegative q G P hLow
  have hMinPacking : ∀ t ∈ P, q ≤ G.degree t + 1 := by
    intro t ht
    rcases hInside t ht with h | h <;> unfold signedDeficiency at h <;> omega
  have hPair := paired_rows_incidence_bound q G hFree P hLow hOpen hCard hMinPacking
  have hHighInt : ((highVertices q G).card : ℤ) ≤ H := by exact_mod_cast hHigh
  have hWeight := full_packing_low_card_add_excess q G P hLow hOutsideUnit
  rw [total_positiveDeficiency_eq_signed_add_high q G hDegree, hTotal] at hWeight
  have hSetCard : ((lowVertices q G \ P).card : ℤ) + P.card = (lowVertices q G).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hLow
  have hCardInt : (P.card : ℤ) = q := by exact_mod_cast hCard
  have haInt : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hOutsideCount : ((lowVertices q G \ P).card : ℤ) ≤ q + H := by
    change (lowVertices q G).card + tau = _ at hWeight
    linarith only [hWeight, hSetCard, hCardInt, hHighInt, htNonnegative, haInt]
  have hZero : (pairedPackingRows G P).card = 0 := by
    rcases pairedPackingRows_card_eq_zero_or_two_le G P with h | h
    · exact h
    · have hTwo : (2 : ℤ) ≤ k := by dsimp only [k]; exact_mod_cast h
      have hHOrder : 4 * (H : ℤ) < q := by exact_mod_cast hHighOrder
      exact False.elim (paired_row_fraction_contradiction (q : ℤ) k tau H (lowVertices q G \ P).card
        (by omega) hHOrder hTwo hkSmall htSmall hPair hOutsideCount)
  refine ⟨?_, htSmall⟩
  intro v hv w hw hAdj
  have hvPaired : v ∈ pairedPackingRows G P := Finset.mem_filter.mpr
    ⟨hv, ⟨w, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v w).mpr hAdj, hw⟩⟩⟩
  rw [Finset.card_eq_zero.mp hZero] at hvPaired
  exact Finset.notMem_empty _ hvPaired


/-- A minimizing extremizer has an independent full low packing at every sufficiently large selected order. -/
theorem claimedBound_uniform_independent_packing (hBound : ClaimedBound) :
    ∃ C K T M R Q E N : ℕ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ k : ℕ, N ≤ 2 ^ (2 * (k + 1)) →
      ∀ G : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2) (cycleGraph 4) →
        (∀ J : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
            triangleWeightedObjective G ≤ triangleWeightedObjective J) →
        2 ^ (2 * (k + 1)) ≤ 4 * C * abovePlaneExcess (2 ^ (2 * (k + 1))) ^ 2 ∧
        (∀ v, G.degree v ≤ 2 ^ (2 * (k + 1)) + 2) ∧
        (highVertices (2 ^ (2 * (k + 1))) G).card ≤ 2611456 * C ∧
        (∑ v, positiveDeficiency (2 ^ (2 * (k + 1))) G v) ≤ 3 * (2 ^ (2 * (k + 1)) : ℕ) ∧
        (∀ v, signedDeficiency (2 ^ (2 * (k + 1))) G v ≤ K) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G,
          ∀ w ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G, ¬G.Adj l w) ∧
        (∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G).card ≤ M) ∧
        (∀ l ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G,
          (triangularRegularNeighbors (2 ^ (2 * (k + 1))) G l).card ≤ 16 ∧
          (positivePartners (2 ^ (2 * (k + 1))) G l).card ≤ R) ∧
        (boundedLightTriangleRegularVertices (2 ^ (2 * (k + 1))) T G).card ≤ 72 ∧
        (∀ v, signedDeficiency (2 ^ (2 * (k + 1))) G v = 0 → (positivePartners (2 ^ (2 * (k + 1))) G v).card ≤ R) ∧
        (∀ v, 1 ≤ signedDeficiency (2 ^ (2 * (k + 1))) G v →
          ((positivePartners (2 ^ (2 * (k + 1))) G v).filter fun y => signedDeficiency (2 ^ (2 * (k + 1))) G y = 0 ∨
            y ∈ boundedLightLowVertices (2 ^ (2 * (k + 1))) T G).card ≤ Q) ∧
        ∃ P : Finset (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          P ⊆ boundedNonlightLowVertices (2 ^ (2 * (k + 1))) T G ∧
          (zeroCodegreeGraph G).IsClique (P : Set _) ∧ P.card = 2 ^ (2 * (k + 1)) ∧
          (∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w) ∧
          8 * (∑ t ∈ P, (signedDeficiency (2 ^ (2 * (k + 1))) G t - 1)) < 2 ^ (2 * (k + 1)) ∧
          (∀ A ⊆ lowVertices (2 ^ (2 * (k + 1))) G, (zeroCodegreeGraph G).IsClique (A : Set _) → A.card ≤ P.card) ∧
          (∀ v ∈ lowVertices (2 ^ (2 * (k + 1))) G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E) ∧
          ∀ v ∈ P, ∀ w ∈ P, v ≠ w → Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  obtain ⟨C, K, T, M, R, Q, E, N₀, hC, hK, hFull⟩ := claimedBound_uniform_full_packing hBound
  let H := 2611456 * C
  let D := 2 + K * M + 72 + H + M + 1
  let W := 18 * (2 * D) ^ 2
  let B := 4 * (2 + E) + (E + 1 + K) * W + K * W ^ 2
  let A := 6 * (2 * D) ^ 2 + B + 2 * H + 60
  let cutoff := N₀ + 4 * C * A ^ 2 + 4 * H + 1024 + 1
  refine ⟨C, K, T, M, R, Q, E, cutoff, hC, hK, ?_⟩
  intro k hk G hFree hEdges hMinimal
  let q := 2 ^ (2 * (k + 1))
  let a := abovePlaneExcess q
  have hCutoff : cutoff ≤ q := hk
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hOrder : 4 * C * A ^ 2 < q := by dsimp only [cutoff] at hCutoff; omega
  have hq : 1024 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hHOrder : 4 * H < q := by dsimp only [cutoff] at hCutoff; omega
  obtain ⟨hExcess, hDegree, hHigh, hPositive, hGlobal, hLightIndependent, hNonlight, hLights,
    hJ, hRegular, hGood, P, hPN, hClique, hCard, hMaximum, hOutside, hDisjoint⟩ := hFull k hN₀ G hFree hEdges
  change q ≤ 4 * C * a ^ 2 at hExcess
  have hLargeA : A < a := by
    by_contra h
    have hSmall : a ≤ A := by omega
    have hSquare := Nat.pow_le_pow_left hSmall 2
    have hScaled := Nat.mul_le_mul_left (4 * C) hSquare
    omega
  have hLow : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hPN hv)).1
  have hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0 := by
    intro v hv w hw hNe
    exact (hClique hv hw hNe).2
  obtain ⟨hInside, hOutsideUnit⟩ := extremal_full_packing_deficiencies q G hFree hEdges P hLow hOpen hCard
  have hMinPacking : ∀ t ∈ P, q ≤ G.degree t + 1 := by
    intro t ht
    rcases hInside t ht with h | h <;> unfold signedDeficiency at h <;> omega
  have ha : 1 ≤ a := by omega
  have hEdgeCount : G.edgeFinset.card = planeEdgeCount q + a := by
    have hPos : 0 < abovePlaneExcess q := by change 0 < a; omega
    unfold abovePlaneExcess at hPos
    change _ = planeEdgeCount q + abovePlaneExcess q
    rw [hEdges]
    unfold abovePlaneExcess
    change extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) = planeEdgeCount q + (extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) - planeEdgeCount q)
    omega
  have hTotal := signedDeficiency_sum_of_excess q a G hEdgeCount
  have hPairSmall := full_packing_paired_fraction_bound q T K M E H a (by omega) G hFree hDegree hGlobal hPositive
    hLightIndependent hNonlight hJ hHigh hTotal P hPN hOpen hCard hMinPacking hOutsideUnit hOutside hLargeA
  obtain ⟨hIndependent, hTauSmall⟩ := minimizing_packing_independent_of_paired_fraction q H a hq hHOrder ha G hFree hDegree hHigh
    hMinimal hPositive hTotal P hLow hCard hOpen hInside hOutsideUnit hPairSmall
  exact ⟨hExcess, hDegree, hHigh, hPositive, hGlobal, hLightIndependent, hNonlight, hLights,
    hJ, hRegular, hGood, P, hPN, hClique, hCard, hIndependent, hTauSmall, hMaximum, hOutside, hDisjoint⟩


/-- Positive neighbor weight bounds the number of low neighbors. -/
theorem low_neighbor_card_le_positive_weight {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    ((lowNeighbors q G v).card : ℤ) ≤ ∑ w ∈ G.neighborFinset v, positiveDeficiency q G w := by
  calc
    _ = ∑ _w ∈ lowNeighbors q G v, (1 : ℤ) := by simp
    _ ≤ ∑ w ∈ lowNeighbors q G v, positiveDeficiency q G w := by
      apply Finset.sum_le_sum
      intro w hw
      have hLow := (Finset.mem_filter.mp hw).2
      unfold positiveDeficiency
      omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun w _ _ => positiveDeficiency_nonnegative q G w)

/-- Triangular regular neighbors contribute to the local triangle-walk count. -/
theorem triangular_regular_card_le_triangleTwice {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    (triangularRegularNeighbors q G v).card ≤ triangleTwice G v := by
  calc
    _ = ∑ _w ∈ triangularRegularNeighbors q G v, 1 := by simp
    _ = ∑ w ∈ triangularRegularNeighbors q G v, codegree G v w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (Finset.mem_filter.mp hw).2.symm
    _ ≤ _ := Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

/-- An independent selected set has no paired rows. -/
theorem pairedPackingRows_empty_of_independent {n : ℕ} (G : SimpleGraph (Fin n)) (P : Finset (Fin n))
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w) : pairedPackingRows G P = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvP, w, hw⟩ := Finset.mem_filter.mp hv
  obtain ⟨hwN, hwP⟩ := Finset.mem_inter.mp hw
  exact hIndependent v hvP w hwP ((G.mem_neighborFinset v w).mp hwN)

/-- Each nonlight outside an independent full packing has linearly many light neighbors. -/
theorem outside_nonlight_light_degree_lower (q T K M : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G) (hCard : P.card = q)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hOutsideUnit : ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1)
    (x : Fin (q ^ 2 + q + 2)) (hx : x ∈ boundedNonlightLowVertices q T G \ P) :
    (q : ℤ) ≤ ((T : ℤ) + 4) * ((G.neighborFinset x ∩ boundedLightLowVertices q T G).card + (K : ℤ) * M) := by
  obtain ⟨hxNL, hxNotP⟩ := Finset.mem_sdiff.mp hx
  have hxLow := (Finset.mem_sdiff.mp hxNL).1
  have hUnit := hOutsideUnit x (Finset.mem_sdiff.mpr ⟨hxLow, hxNotP⟩)
  have hLowP : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  let b : ℤ := (G.neighborFinset x ∩ boundedLightLowVertices q T G).card + (K : ℤ) * M
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hWeight : (∑ w ∈ G.neighborFinset x, positiveDeficiency q G w) ≤ b := by
    have h := bounded_neighbor_positive_weight q T (K : ℤ) (Int.natCast_nonneg K) G hGlobal x
    have hCardNL : ((G.neighborFinset x ∩ boundedNonlightLowVertices q T G).card : ℤ) ≤ M := by exact_mod_cast hNonlight x
    have hScale := mul_le_mul_of_nonneg_left hCardNL (Int.natCast_nonneg K)
    dsimp only [b]
    linarith only [h, hScale]
  rcases Finset.mem_union.mp (boundedNonlightLowVertices_subset q T G hxNL) with hHub | hActive
  · have hHubDegree := (Finset.mem_filter.mp hHub).2
    have hLowDegree := low_neighbor_card_le_positive_weight q G x
    have hScale := mul_le_mul_of_nonneg_left (hLowDegree.trans hWeight) (Int.natCast_nonneg T)
    have hEnlarge := mul_nonneg (show (0 : ℤ) ≤ 4 by norm_num) hb
    change (q : ℤ) ≤ ((T : ℤ) + 4) * b
    linarith only [hHubDegree, hScale, hEnlarge]
  · have hHeavy : (q : ℤ) ≤ 2 * (triangularRegularNeighbors q G x).card := by
      rcases (Finset.mem_filter.mp hActive).2 with hNonunit | hHeavy
      · omega
      · exact hHeavy
    have hExchange := minimizing_outside_unit_exchange q G hFree hMinimal P hCard hOpen x hxNotP hUnit
    rw [pairedPackingRows_empty_of_independent G P hIndependent, Finset.card_empty, Nat.cast_zero, add_zero] at hExchange
    have hTau := packing_excess_nonnegative q G P hLowP
    have hSigned : (∑ w ∈ G.neighborFinset x, signedDeficiency q G w) ≤ b :=
      (Finset.sum_le_sum (fun _ _ => le_max_left _ _)).trans hWeight
    have hTri : ((triangularRegularNeighbors q G x).card : ℤ) ≤ triangleTwice G x := by
      exact_mod_cast triangular_regular_card_le_triangleTwice q G x
    have hInternal : (0 : ℤ) ≤ (G.neighborFinset x ∩ P).card := Int.natCast_nonneg _
    have hEnlarge := mul_nonneg (Int.natCast_nonneg T) hb
    change (q : ℤ) ≤ ((T : ℤ) + 4) * b
    linarith only [hHeavy, hTri, hExchange, hTau, hSigned, hInternal, hEnlarge]

/-- Only boundedly many nonlights can lie outside an independent full packing. -/
theorem outside_nonlight_card_le (q T K M : ℕ) (hq : 0 < q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hPositive : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ))
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G) (hCard : P.card = q)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hOutsideUnit : ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1)
    (hOrder : 2 * (T + 4) * K * M ≤ q) :
    (boundedNonlightLowVertices q T G \ P).card ≤ 6 * (T + 4) * M := by
  let D := boundedNonlightLowVertices q T G \ P
  let L := boundedLightLowVertices q T G
  have hEach (v) (hv : v ∈ D) : (q : ℤ) ≤ 2 * ((T : ℤ) + 4) * (G.neighborFinset v ∩ L).card := by
    have h := outside_nonlight_light_degree_lower q T K M G hFree hGlobal hNonlight hMinimal P hP hCard hOpen hIndependent hOutsideUnit v hv
    have hOrderInt : 2 * ((T : ℤ) + 4) * K * M ≤ q := by exact_mod_cast hOrder
    dsimp only [L]
    nlinarith only [h, hOrderInt]
  have hSum := Finset.sum_le_sum hEach
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hSum
  have hSwap : (∑ v ∈ D, ((G.neighborFinset v ∩ L).card : ℤ)) =
      ∑ w ∈ L, ((G.neighborFinset w ∩ D).card : ℤ) := by exact_mod_cast sum_neighbor_intersection_card G D L
  have hIncidence : (∑ w ∈ L, ((G.neighborFinset w ∩ D).card : ℤ)) ≤ (M : ℤ) * L.card := by
    calc
      _ ≤ ∑ _w ∈ L, (M : ℤ) := by
        apply Finset.sum_le_sum
        intro w _
        have hSubset : G.neighborFinset w ∩ D ⊆ G.neighborFinset w ∩ boundedNonlightLowVertices q T G := by
          intro v hv
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).1⟩
        exact_mod_cast (Finset.card_le_card hSubset).trans (hNonlight w)
      _ = _ := by simp [mul_comm]
  have hLightSubset : L ⊆ lowVertices q G := by
    intro v hv
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hLightCard : (L.card : ℤ) ≤ 3 * q := by
    have hC : (L.card : ℤ) ≤ (lowVertices q G).card := by exact_mod_cast Finset.card_le_card hLightSubset
    exact hC.trans ((lowVertices_card_le_positiveDeficiency q G).trans hPositive)
  rw [hSwap] at hSum
  have hScale := mul_le_mul_of_nonneg_left hIncidence (show 0 ≤ 2 * ((T : ℤ) + 4) by positivity)
  have hScaleLight := mul_le_mul_of_nonneg_left hLightCard (show 0 ≤ 2 * ((T : ℤ) + 4) * M by positivity)
  have hFinal : (D.card : ℤ) * q ≤ (6 * ((T : ℤ) + 4) * M) * q := by nlinarith only [hSum, hScale, hScaleLight]
  have hqInt : (0 : ℤ) < q := by exact_mod_cast hq
  have hBound := (mul_le_mul_iff_of_pos_right hqInt).mp hFinal
  exact_mod_cast hBound

/-- Maximality and linear nonlight degree eliminate the bounded outside nonlight set. -/
theorem outside_lows_are_light (q T K M E Q H : ℕ) (hq : 0 < q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hGlobal : ∀ v, signedDeficiency q G v ≤ K)
    (hPositive : (∑ v, positiveDeficiency q G v) ≤ 3 * (q : ℤ))
    (hNonlight : ∀ v, (G.neighborFinset v ∩ boundedNonlightLowVertices q T G).card ≤ M)
    (hHigh : (highVertices q G).card ≤ H)
    (hRows : ∀ v, 1 ≤ signedDeficiency q G v →
      ((positivePartners q G v).filter fun w => signedDeficiency q G w = 0 ∨ w ∈ boundedLightLowVertices q T G).card ≤ Q)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hP : P ⊆ boundedNonlightLowVertices q T G) (hCard : P.card = q)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hOutsideUnit : ∀ v ∈ lowVertices q G \ P, signedDeficiency q G v = 1)
    (hOutside : ∀ v ∈ lowVertices q G, v ∉ P → ((zeroCodegreeGraph G).neighborFinset v ∩ P).card ≤ E)
    (hOrder : 2 * (T + 4) * K * M ≤ q)
    (hRowsOrder : 2 * (T + 2) * (Q + 2 * H) ≤ q)
    (hLarge : 2 * (T + 2) * (E + 6 * (T + 4) * M) < q) :
    lowVertices q G \ P ⊆ boundedLightLowVertices q T G := by
  have hOutsideNL := outside_nonlight_card_le q T K M hq G hFree hGlobal hPositive hNonlight hMinimal P hP hCard hOpen hIndependent hOutsideUnit hOrder
  have hActualOrder : 2 * (T + 2) * (Q + 2 * (highVertices q G).card) ≤ q := by
    calc
      _ ≤ 2 * (T + 2) * (Q + 2 * H) := by gcongr
      _ ≤ _ := hRowsOrder
  intro v hv
  obtain ⟨hvLow, hvNotP⟩ := Finset.mem_sdiff.mp hv
  by_contra hvNotLight
  have hvNL : v ∈ boundedNonlightLowVertices q T G := Finset.mem_sdiff.mpr ⟨hvLow, hvNotLight⟩
  have hMany := bounded_nonlight_zero_degree_linear q T Q G hFree hDegree hRows hActualOrder v hvNL
  have hCover : nonlightZeroNeighbors q T G v ⊆
      ((zeroCodegreeGraph G).neighborFinset v ∩ P) ∪ (boundedNonlightLowVertices q T G \ P) := by
    intro w hw
    obtain ⟨hwZ, hwNL⟩ := Finset.mem_inter.mp hw
    by_cases hwP : w ∈ P
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hwZ, hwP⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwNL, hwP⟩)
  have hFew := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hCount : (nonlightZeroNeighbors q T G v).card ≤ E + 6 * (T + 4) * M := by
    have hOutsideV := hOutside v hvLow hvNotP
    omega
  have hScaled := Nat.mul_le_mul_left (2 * (T + 2)) hCount
  omega


/-- Once every outside low is light, all nonlight vertices belong to the packing. -/
theorem nonlight_subset_packing_of_outside_light {n : ℕ} (q T : ℕ) (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (hOutside : lowVertices q G \ P ⊆ boundedLightLowVertices q T G) :
    boundedNonlightLowVertices q T G ⊆ P := by
  intro v hv
  obtain ⟨hvLow, hvNotLight⟩ := Finset.mem_sdiff.mp hv
  by_contra hvNotP
  exact hvNotLight (hOutside (Finset.mem_sdiff.mpr ⟨hvLow, hvNotP⟩))

/-- A deficiency-two row has many untriangulated regular neighbors when all nonlights lie in the packing. -/
theorem deep_untriangulated_regular_lower (q T Q H : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hHigh : (highVertices q G).card ≤ H)
    (hRows : ∀ v, 1 ≤ signedDeficiency q G v →
      ((positivePartners q G v).filter fun w => signedDeficiency q G w = 0 ∨ w ∈ boundedLightLowVertices q T G).card ≤ Q)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hCard : P.card = q) (hNonlight : boundedNonlightLowVertices q T G ⊆ P)
    (t : Fin (q ^ 2 + q + 2)) (hDeep : signedDeficiency q G t = 2) :
    (q : ℤ) ≤ (regularNeighbors q G t \ triangularRegularNeighbors q G t).card + Q + 3 * H := by
  have hRow := positivePartners_le_nonlightZeroNeighbors_add q T Q G t (by omega) (hRows t (by omega))
  have hSubset : nonlightZeroNeighbors q T G t ⊆ P := fun _ hv => hNonlight (Finset.mem_inter.mp hv).2
  have hZCard := (Finset.card_le_card hSubset).trans_eq hCard
  have hPositiveBound : ((positivePartners q G t).card : ℤ) ≤ q + Q + H := by
    exact_mod_cast (show (positivePartners q G t).card ≤ q + Q + H by omega)
  have hExact := nonunit_positivePartners_card q G hFree hDegree t (by omega)
  rw [hDeep] at hExact
  have hTriangleSum : (∑ w ∈ G.neighborFinset t, (codegree G t w : ℤ)) = (triangleTwice G t : ℤ) := by
    simp [triangleTwice]
  rw [hTriangleSum] at hExact
  have hLowDegree := low_degree_le_neighbor_signed_add_high q G hDegree t
  have hRegular := regular_neighbor_card_lower q G t
  have hTriangles : ((triangularRegularNeighbors q G t).card : ℤ) ≤ triangleTwice G t := by
    exact_mod_cast triangular_regular_card_le_triangleTwice q G t
  have hPartition : ((regularNeighbors q G t \ triangularRegularNeighbors q G t).card : ℤ) +
      (triangularRegularNeighbors q G t).card = (regularNeighbors q G t).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hDegreeInt : (G.degree t : ℤ) + 1 = q := by unfold signedDeficiency at hDeep; omega
  have hHighInt : ((highVertices q G).card : ℤ) ≤ H := by exact_mod_cast hHigh
  nlinarith only [hPositiveBound, hExact, hLowDegree, hRegular, hTriangles, hPartition, hDegreeInt, hHighInt]

/-- A light vertex cannot be adjacent to a deep packing row at sufficiently large order. -/
theorem no_deep_light_edge (q T Q R H : ℕ) (hq : R + Q + 3 * H < q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2) (hHigh : (highVertices q G).card ≤ H)
    (hRows : ∀ v, 1 ≤ signedDeficiency q G v →
      ((positivePartners q G v).filter fun w => signedDeficiency q G w = 0 ∨ w ∈ boundedLightLowVertices q T G).card ≤ Q)
    (hLightRows : ∀ l ∈ boundedLightLowVertices q T G, (positivePartners q G l).card ≤ R)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hCard : P.card = q) (hOutside : lowVertices q G \ P ⊆ boundedLightLowVertices q T G)
    (t l : Fin (q ^ 2 + q + 2)) (hDeep : signedDeficiency q G t = 2) (hl : l ∈ boundedLightLowVertices q T G) :
    ¬G.Adj t l := by
  intro hAdj
  have hUnit := (Finset.mem_filter.mp hl).2.1
  have hCover := adjacent_low_untriangulated_card_le q G hFree t l hAdj (by omega) hUnit
  have hSubset : triangularRegularNeighbors q G t ⊆ regularNeighbors q G t := Finset.filter_subset _ _
  have hPartition := Finset.card_sdiff_add_card_eq_card hSubset
  have hSmall : (regularNeighbors q G t \ triangularRegularNeighbors q G t).card ≤ R := by
    have hRowsL := hLightRows l hl
    omega
  have hSmallInt : ((regularNeighbors q G t \ triangularRegularNeighbors q G t).card : ℤ) ≤ R := by exact_mod_cast hSmall
  have hLower := deep_untriangulated_regular_lower q T Q H G hFree hDegree hHigh hRows P hCard
    (nonlight_subset_packing_of_outside_light q T G P hOutside) t hDeep
  have hqInt : (R : ℤ) + Q + 3 * H < q := by exact_mod_cast hq
  linarith


/-- An outside light forces zero packing excess, no local triangles, and no high neighbor. -/
theorem outside_light_exchange_consequences (q T : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (hLightIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G) (hCard : P.card = q)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hInside : ∀ v ∈ P, signedDeficiency q G v = 1 ∨ signedDeficiency q G v = 2)
    (hOutside : lowVertices q G \ P ⊆ boundedLightLowVertices q T G)
    (hNoDeep : ∀ t ∈ P, signedDeficiency q G t = 2 → ∀ l ∈ boundedLightLowVertices q T G, ¬G.Adj t l)
    (x : Fin (q ^ 2 + q + 2)) (hx : x ∈ lowVertices q G \ P) :
    (∑ t ∈ P, (signedDeficiency q G t - 1)) = 0 ∧ triangleTwice G x = 0 ∧
      (G.neighborFinset x ∩ highVertices q G).card = 0 := by
  have hxLight := hOutside hx
  have hxUnit := (Finset.mem_filter.mp hxLight).2.1
  have hxNot := (Finset.mem_sdiff.mp hx).2
  have hEach (v) (hv : v ∈ G.neighborFinset x) :
      positiveDeficiency q G v = if v ∈ P then 1 else 0 := by
    have hxv := (G.mem_neighborFinset x v).mp hv
    by_cases hvP : v ∈ P
    · rcases hInside v hvP with hUnit | hDeep
      · simp [positiveDeficiency, hUnit, hvP]
      · exact False.elim (hNoDeep v hvP hDeep x hxLight hxv.symm)
    · have hNonpositive : signedDeficiency q G v ≤ 0 := by
        by_contra h
        have hvLow : v ∈ lowVertices q G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have hvLight := hOutside (Finset.mem_sdiff.mpr ⟨hvLow, hvP⟩)
        exact hLightIndependent x hxLight v hvLight hxv
      simp only [ite_eq_right hvP, positiveDeficiency, max_eq_right hNonpositive]
  have hPositive : (∑ v ∈ G.neighborFinset x, positiveDeficiency q G v) = (G.neighborFinset x ∩ P).card := by
    rw [Finset.sum_congr rfl hEach]
    simpa only [one_mul] using neighbor_indicator_weight_sum G x P (1 : ℤ)
  have hWeights := sum_positiveDeficiency_eq_signed_add_high q G hDegree (G.neighborFinset x)
  rw [hPositive] at hWeights
  have hExchange := minimizing_outside_unit_exchange q G hFree hMinimal P hCard hOpen x hxNot hxUnit
  rw [pairedPackingRows_empty_of_independent G P hIndependent, Finset.card_empty, Nat.cast_zero, add_zero] at hExchange
  have hTau := packing_excess_nonnegative q G P hLow
  have hTri : (0 : ℤ) ≤ triangleTwice G x := Int.natCast_nonneg _
  have hHigh : (0 : ℤ) ≤ (G.neighborFinset x ∩ highVertices q G).card := Int.natCast_nonneg _
  have hTauZero : (∑ t ∈ P, (signedDeficiency q G t - 1)) = 0 := by linarith
  have hTriZero : (triangleTwice G x : ℤ) = 0 := by linarith
  have hHighZero : ((G.neighborFinset x ∩ highVertices q G).card : ℤ) = 0 := by linarith
  exact ⟨hTauZero, by exact_mod_cast hTriZero, by exact_mod_cast hHighZero⟩

/-- High vertices are excluded once outside lights have no deep neighbor. -/
theorem full_packing_no_high (q T : ℕ) (hq : 4 ≤ q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (hLightIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G) (hCard : P.card = q)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hInside : ∀ v ∈ P, signedDeficiency q G v = 1 ∨ signedDeficiency q G v = 2)
    (hOutside : lowVertices q G \ P ⊆ boundedLightLowVertices q T G)
    (hNoDeep : ∀ t ∈ P, signedDeficiency q G t = 2 → ∀ l ∈ boundedLightLowVertices q T G, ¬G.Adj t l) :
    ∀ v, 0 ≤ signedDeficiency q G v := by
  intro v
  by_contra hNegative
  have hvHigh : v ∈ highVertices q G := (mem_highVertices_iff q G v).mpr (by omega)
  have hHighDegree : q + 2 ≤ G.degree v := by unfold signedDeficiency at hNegative; omega
  have hWeightLower := high_vertex_positive_neighbor_sum q G hFree v hHighDegree
  have hEach (w) (hw : w ∈ G.neighborFinset v) :
      positiveDeficiency q G w ≤ if w ∈ P then 2 else 0 := by
    by_cases hwP : w ∈ P
    · rcases hInside w hwP with h | h <;> simp [positiveDeficiency, hwP, h]
    · have hNonpositive : signedDeficiency q G w ≤ 0 := by
        by_contra h
        have hwLow : w ∈ lowVertices q G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have hwOutside := Finset.mem_sdiff.mpr ⟨hwLow, hwP⟩
        have hConsequences := outside_light_exchange_consequences q T G hFree hDegree hMinimal hLightIndependent P hLow hCard hOpen hIndependent hInside hOutside hNoDeep w hwOutside
        have hMember : v ∈ G.neighborFinset w ∩ highVertices q G := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w v).mpr ((G.mem_neighborFinset v w).mp hw).symm, hvHigh⟩
        have hPositive := Finset.card_pos.mpr ⟨v, hMember⟩
        omega
      simp [positiveDeficiency, hwP, max_eq_right hNonpositive]
  have hUpper := Finset.sum_le_sum hEach
  have hSum := neighbor_indicator_weight_sum G v P (2 : ℤ)
  rw [hSum] at hUpper
  have hCardBound : ((G.neighborFinset v ∩ P).card : ℤ) ≤ 1 := by
    exact_mod_cast open_packing_neighbor_card_le_one G P hOpen v
  have hqInt : (4 : ℤ) ≤ q := by exact_mod_cast hq
  linarith

/-- The independent full packing has no excess once the high set has vanished. -/
theorem full_packing_excess_eq_zero (q T a : ℕ) (hq : 4 ≤ q) (hEven : Even q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (hLightIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G) (hCard : P.card = q)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hInside : ∀ v ∈ P, signedDeficiency q G v = 1 ∨ signedDeficiency q G v = 2)
    (hOutside : lowVertices q G \ P ⊆ boundedLightLowVertices q T G)
    (hNoDeep : ∀ t ∈ P, signedDeficiency q G t = 2 → ∀ l ∈ boundedLightLowVertices q T G, ¬G.Adj t l) :
    (∑ t ∈ P, (signedDeficiency q G t - 1)) = 0 := by
  by_cases hOutsideEmpty : lowVertices q G \ P = ∅
  · let tau : ℤ := ∑ t ∈ P, (signedDeficiency q G t - 1)
    have hNonnegative := full_packing_no_high q T hq G hFree hDegree hMinimal hLightIndependent P hLow hCard hOpen hIndependent hInside hOutside hNoDeep
    have hLowSubset : lowVertices q G ⊆ P := Finset.sdiff_eq_empty_iff_subset.mp hOutsideEmpty
    have hLowEq : lowVertices q G = P := Finset.Subset.antisymm hLowSubset hLow
    have hTau : 0 ≤ tau := packing_excess_nonnegative q G P hLow
    by_contra hNotZero
    have hTauPos : 0 < tau := by omega
    have hDeepCard : ((P.filter fun v => signedDeficiency q G v = 2).card : ℤ) = tau :=
      (full_packing_excess_eq_deep_card q G P hInside).symm
    have hDeepNonempty : (P.filter fun v => signedDeficiency q G v = 2).Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast (show (0 : ℤ) < (P.filter fun v => signedDeficiency q G v = 2).card by omega)
    obtain ⟨v, hv⟩ := hDeepNonempty
    obtain ⟨hvP, hvDeep⟩ := Finset.mem_filter.mp hv
    have hWeights : (∑ w ∈ G.neighborFinset v, signedDeficiency q G w) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hwNotP : w ∉ P := fun hwP => hIndependent v hvP w hwP ((G.mem_neighborFinset v w).mp hw)
      have hwNonpositive : signedDeficiency q G w ≤ 0 := by
        by_contra h
        exact hwNotP (hLowSubset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
      exact le_antisymm hwNonpositive (hNonnegative w)
    have hExchange := minimizing_deep_packing_exchange q G hFree hMinimal P hCard hOpen v hvP hvDeep
    rw [hWeights, pairedPackingRows_empty_of_independent G P hIndependent, Finset.card_empty, Nat.cast_zero] at hExchange
    have hTriangle : (0 : ℤ) ≤ triangleTwice G v := Int.natCast_nonneg _
    have hInternal : (0 : ℤ) ≤ (G.neighborFinset v ∩ P).card := Int.natCast_nonneg _
    have hTauOne : tau = 1 := by change 2 * tau + _ ≤ _ at hExchange; omega
    have hOutsideUnit : ∀ w ∈ lowVertices q G \ P, signedDeficiency q G w = 1 := by
      intro w hw
      rw [hOutsideEmpty] at hw
      exact False.elim (Finset.notMem_empty w hw)
    have hWeight := full_packing_low_card_add_excess q G P hLow hOutsideUnit
    have hAllPositive : (∑ w, positiveDeficiency q G w) = ∑ w, signedDeficiency q G w := by
      apply Finset.sum_congr rfl
      intro w _
      exact max_eq_left (hNonnegative w)
    rw [hAllPositive, hLowEq, hCard, hTotal] at hWeight
    change (q : ℤ) + tau = _ at hWeight
    obtain ⟨b, hb⟩ := hEven
    omega
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hOutsideEmpty
    exact (outside_light_exchange_consequences q T G hFree hDegree hMinimal hLightIndependent P hLow hCard hOpen hIndependent hInside hOutside hNoDeep x hx).1


/-- A triangle-free row has zero codegree with each of its graph neighbors. -/
theorem triangleTwice_zero_adj_codegree {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n)
    (hZero : triangleTwice G x = 0) (hAdj : G.Adj x y) : codegree G x y = 0 := by
  have hBound : codegree G x y ≤ triangleTwice G x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) ((G.mem_neighborFinset x y).mpr hAdj)
  omega

/-- The finite exchange argument leaves only unit lows and triangle-free outside lows. -/
theorem full_packing_unit_structure (q T a : ℕ) (hq : 4 ≤ q) (hEven : Even q)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hDegree : ∀ v, G.degree v ≤ q + 2)
    (hMinimal : ∀ J : SimpleGraph (Fin (q ^ 2 + q + 2)), (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card →
      triangleWeightedObjective G ≤ triangleWeightedObjective J)
    (hLightIndependent : ∀ l ∈ boundedLightLowVertices q T G, ∀ w ∈ boundedLightLowVertices q T G, ¬G.Adj l w)
    (hTotal : (∑ v, signedDeficiency q G v) = 2 * (q : ℤ) + 2 - 2 * a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hLow : P ⊆ lowVertices q G) (hCard : P.card = q)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hInside : ∀ v ∈ P, signedDeficiency q G v = 1 ∨ signedDeficiency q G v = 2)
    (hOutside : lowVertices q G \ P ⊆ boundedLightLowVertices q T G)
    (hNoDeep : ∀ t ∈ P, signedDeficiency q G t = 2 → ∀ l ∈ boundedLightLowVertices q T G, ¬G.Adj t l) :
    (∀ v, signedDeficiency q G v = 0 ∨ signedDeficiency q G v = 1) ∧
    (∀ t ∈ P, signedDeficiency q G t = 1) ∧
    (∀ x ∈ lowVertices q G \ P, triangleTwice G x = 0) ∧
    (∀ x ∈ lowVertices q G \ P, ∀ y ∈ lowVertices q G \ P, ¬G.Adj x y) := by
  have hNonnegative := full_packing_no_high q T hq G hFree hDegree hMinimal hLightIndependent P hLow hCard hOpen hIndependent hInside hOutside hNoDeep
  have hTau := full_packing_excess_eq_zero q T a hq hEven G hFree hDegree hMinimal hLightIndependent hTotal P hLow hCard hOpen hIndependent hInside hOutside hNoDeep
  have hDeepCard := full_packing_excess_eq_deep_card q G P hInside
  rw [hTau] at hDeepCard
  have hEmpty : (P.filter fun t => signedDeficiency q G t = 2) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact_mod_cast hDeepCard.symm
  have hUnit (t) (ht : t ∈ P) : signedDeficiency q G t = 1 := by
    rcases hInside t ht with h | h
    · exact h
    · have hMem : t ∈ P.filter (fun t => signedDeficiency q G t = 2) := Finset.mem_filter.mpr ⟨ht, h⟩
      rw [hEmpty] at hMem
      exact False.elim (Finset.notMem_empty _ hMem)
  refine ⟨?_, hUnit, ?_, ?_⟩
  · intro v
    by_cases hvP : v ∈ P
    · exact Or.inr (hUnit v hvP)
    · by_cases hvLow : v ∈ lowVertices q G
      · have hvLight := hOutside (Finset.mem_sdiff.mpr ⟨hvLow, hvP⟩)
        exact Or.inr (Finset.mem_filter.mp hvLight).2.1
      · have hNonpositive : signedDeficiency q G v ≤ 0 := by
          by_contra h
          exact hvLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
        exact Or.inl (le_antisymm hNonpositive (hNonnegative v))
  · intro x hx
    exact (outside_light_exchange_consequences q T G hFree hDegree hMinimal hLightIndependent P hLow hCard hOpen hIndependent hInside hOutside hNoDeep x hx).2.1
  · intro x hx y hy
    exact hLightIndependent x (hOutside hx) y (hOutside hy)

/-- Every sufficiently large minimizing extremizer admits the normalized packing needed for completion. -/
theorem claimedBound_uniform_normalized_packing (hBound : ClaimedBound) :
    ∃ C N : ℕ, 1 ≤ C ∧ ∀ k : ℕ, N ≤ 2 ^ (2 * (k + 1)) →
      ∀ G : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)), (cycleGraph 4).Free G →
        G.edgeFinset.card = extremalNumber ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2) (cycleGraph 4) →
        (∀ J : SimpleGraph (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          (cycleGraph 4).Free J → J.edgeFinset.card = G.edgeFinset.card → triangleWeightedObjective G ≤ triangleWeightedObjective J) →
        2 ^ (2 * (k + 1)) ≤ 4 * C * abovePlaneExcess (2 ^ (2 * (k + 1))) ^ 2 ∧
        ∃ P : Finset (Fin ((2 ^ (2 * (k + 1))) ^ 2 + 2 ^ (2 * (k + 1)) + 2)),
          P.card = 2 ^ (2 * (k + 1)) ∧ P ⊆ lowVertices (2 ^ (2 * (k + 1))) G ∧
          (∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0) ∧
          (∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w) ∧
          (∀ v, signedDeficiency (2 ^ (2 * (k + 1))) G v = 0 ∨ signedDeficiency (2 ^ (2 * (k + 1))) G v = 1) ∧
          (∀ t ∈ P, signedDeficiency (2 ^ (2 * (k + 1))) G t = 1) ∧
          (∀ x ∈ lowVertices (2 ^ (2 * (k + 1))) G \ P, triangleTwice G x = 0) ∧
          (∀ x ∈ lowVertices (2 ^ (2 * (k + 1))) G \ P, ∀ y ∈ lowVertices (2 ^ (2 * (k + 1))) G \ P, ¬G.Adj x y) := by
  obtain ⟨C, K, T, M, R, Q, E, N₀, hC, _hK, hPrepared⟩ := claimedBound_uniform_independent_packing hBound
  let H := 2611456 * C
  let cutoff := N₀ + 2 * (T + 4) * K * M + 2 * (T + 2) * (Q + 2 * H) +
    2 * (T + 2) * (E + 6 * (T + 4) * M) + R + Q + 3 * H + 5
  refine ⟨C, cutoff, hC, ?_⟩
  intro k hk G hFree hEdges hMinimal
  let q := 2 ^ (2 * (k + 1))
  let a := abovePlaneExcess q
  have hCutoff : cutoff ≤ q := hk
  have hN₀ : N₀ ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hq : 4 ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hOrder : 2 * (T + 4) * K * M ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hRowsOrder : 2 * (T + 2) * (Q + 2 * H) ≤ q := by dsimp only [cutoff] at hCutoff; omega
  have hLarge : 2 * (T + 2) * (E + 6 * (T + 4) * M) < q := by dsimp only [cutoff] at hCutoff; omega
  have hDeepOrder : R + Q + 3 * H < q := by dsimp only [cutoff] at hCutoff; omega
  obtain ⟨hExcess, hDegree, hHigh, hPositive, hGlobal, hLightIndependent, hNonlight, hLights,
    hJ, hRegular, hGood, P, hPN, hClique, hCard, hIndependent, _hTauSmall, hMaximum, hOutside, hDisjoint⟩ :=
      hPrepared k hN₀ G hFree hEdges hMinimal
  have hLow : P ⊆ lowVertices q G := fun _ hv => (Finset.mem_sdiff.mp (hPN hv)).1
  have hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0 := by
    intro v hv w hw hNe
    exact (hClique hv hw hNe).2
  obtain ⟨hInside, hOutsideUnit⟩ := extremal_full_packing_deficiencies q G hFree hEdges P hLow hOpen hCard
  have hOutsideLight := outside_lows_are_light q T K M E Q H (by omega) G hFree hDegree hGlobal hPositive hNonlight hHigh hGood
    hMinimal P hPN hCard hOpen hIndependent hOutsideUnit hOutside hOrder hRowsOrder hLarge
  have hNoDeep : ∀ t ∈ P, signedDeficiency q G t = 2 → ∀ l ∈ boundedLightLowVertices q T G, ¬G.Adj t l := by
    intro t _ht ht l hl
    exact no_deep_light_edge q T Q R H hDeepOrder G hFree hDegree hHigh hGood (fun v hv => (hLights v hv).2)
      P hCard hOutsideLight t l ht hl
  have hEven : Even q := by
    refine ⟨2 ^ (2 * k + 1), ?_⟩
    dsimp only [q]
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    omega
  have hAPos : 0 < a := by
    by_contra h
    have hZero : a = 0 := by omega
    change q ≤ 4 * C * a ^ 2 at hExcess
    rw [hZero] at hExcess
    norm_num at hExcess
    omega
  have hEdgeCount : G.edgeFinset.card = planeEdgeCount q + a := by
    have hPos : 0 < abovePlaneExcess q := hAPos
    unfold abovePlaneExcess at hPos
    change _ = planeEdgeCount q + abovePlaneExcess q
    rw [hEdges]
    unfold abovePlaneExcess
    change extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) = planeEdgeCount q + (extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) - planeEdgeCount q)
    omega
  have hTotal := signedDeficiency_sum_of_excess q a G hEdgeCount
  have hStructure := full_packing_unit_structure q T a hq hEven G hFree hDegree hMinimal hLightIndependent hTotal
    P hLow hCard hOpen hIndependent hInside hOutsideLight hNoDeep
  exact ⟨hExcess, P, hCard, hLow, hOpen, hIndependent, hStructure⟩

end












end

end Erdos60Private


open Filter SimpleGraph Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- Add a looped parent on the packing and a loop on each outside low. -/
def packingCompletion {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℤ
  | none, none => 1
  | none, some v => if v ∈ P then 1 else 0
  | some v, none => if v ∈ P then 1 else 0
  | some v, some w => (G.adjMatrix ℤ + Matrix.diagonal (fun x : Fin n => if x ∈ lowVertices q G \ P then (1 : ℤ) else 0) : Matrix (Fin n) (Fin n) ℤ) v w

/-- The completed incidence matrix is symmetric. -/
theorem packingCompletion_symmetric {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) :
    (packingCompletion q G P).IsSymm := by
  change (packingCompletion q G P)ᵀ = packingCompletion q G P
  ext i j
  cases i with
  | none => cases j <;> rfl
  | some v =>
    cases j with
    | none => rfl
    | some w =>
      by_cases h : v = w
      · subst w
        rfl
      · simp [packingCompletion, Matrix.transpose_apply, h, Ne.symm h, G.adj_comm]

/-- Every entry of the completed matrix is zero or one. -/
theorem packingCompletion_binary {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n))
    (i j : Option (Fin n)) : packingCompletion q G P i j = 0 ∨ packingCompletion q G P i j = 1 := by
  cases i with
  | none =>
    cases j with
    | none => exact Or.inr rfl
    | some v => by_cases h : v ∈ P <;> simp [packingCompletion, h]
  | some v =>
    cases j with
    | none => by_cases h : v ∈ P <;> simp [packingCompletion, h]
    | some w =>
      by_cases h : v = w
      · subst w
        by_cases hX : v ∈ lowVertices q G \ P
        · right
          simp only [packingCompletion, Matrix.add_apply, Matrix.diagonal_apply_eq, ite_eq_left hX]
          simp
        · left
          simp only [packingCompletion, Matrix.add_apply, Matrix.diagonal_apply_eq, ite_eq_right hX]
          simp
      · by_cases hAdj : G.Adj v w <;> simp [packingCompletion, h, hAdj]

/-- The new parent row contains its loop and one entry for each packing vertex. -/
theorem packingCompletion_parent_row_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) :
    (∑ j, packingCompletion q G P none j) = 1 + (P.card : ℤ) := by
  simp [Fintype.sum_option, packingCompletion]

/-- An old row gains its parent incidence or its outside-low loop. -/
theorem packingCompletion_old_row_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) (v : Fin n) :
    (∑ j, packingCompletion q G P (some v) j) =
      (G.degree v : ℤ) + (if v ∈ P then 1 else 0) + (if v ∈ lowVertices q G \ P then 1 else 0) := by
  have hAdj : (∑ w, G.adjMatrix ℤ v w) = (G.degree v : ℤ) := by
    simpa only [Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree, G.adjMatrix_apply] using
      (neighbor_intersection_card_eq_sum_adjacency G Finset.univ v).symm
  simp only [Fintype.sum_option, packingCompletion, Matrix.add_apply, Finset.sum_add_distrib]
  simp only [Matrix.diagonal_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hAdj]
  ring

/-- Unit deficiency makes every completed row have sum q+1. -/
theorem packingCompletion_row_sum {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n))
    (hCard : P.card = q) (hLow : P ⊆ lowVertices q G)
    (hUnit : ∀ v, signedDeficiency q G v = 0 ∨ signedDeficiency q G v = 1) :
    ∀ i, (∑ j, packingCompletion q G P i j) = (q : ℤ) + 1 := by
  intro i
  cases i with
  | none => rw [packingCompletion_parent_row_sum, hCard]; ring
  | some v =>
    rw [packingCompletion_old_row_sum]
    have hIndicator : (if v ∈ P then (1 : ℤ) else 0) + (if v ∈ lowVertices q G \ P then 1 else 0) = signedDeficiency q G v := by
      by_cases hvP : v ∈ P
      · have hvLow := (Finset.mem_filter.mp (hLow hvP)).2
        have hf : signedDeficiency q G v = 1 := by rcases hUnit v with h | h <;> omega
        have hvNot : v ∉ lowVertices q G \ P := fun h => (Finset.mem_sdiff.mp h).2 hvP
        simp [hvP, hvNot, hf]
      · by_cases hvLow : v ∈ lowVertices q G
        · have hPos := (Finset.mem_filter.mp hvLow).2
          have hf : signedDeficiency q G v = 1 := by rcases hUnit v with h | h <;> omega
          have hvX := Finset.mem_sdiff.mpr ⟨hvLow, hvP⟩
          simp [hvP, hvX, hf]
        · have hNotX : v ∉ lowVertices q G \ P := fun h => hvLow (Finset.mem_sdiff.mp h).1
          have hf : signedDeficiency q G v = 0 := by
            rcases hUnit v with h | h
            · exact h
            · exact False.elim (hvLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
          simp [hvP, hNotX, hf]
    have hDegree : (G.degree v : ℤ) + signedDeficiency q G v = (q : ℤ) + 1 := by unfold signedDeficiency; ring
    linarith

/-- The trace counts the new parent loop and the outside-low loops. -/
theorem packingCompletion_trace {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) :
    Matrix.trace (packingCompletion q G P) = 1 + ((lowVertices q G \ P).card : ℤ) := by
  have hSet : (Finset.univ.filter fun x => x ∈ lowVertices q G ∧ x ∉ P) = lowVertices q G \ P := by ext x; simp
  simpa [Matrix.trace, Fintype.sum_option, packingCompletion] using congrArg (fun S : Finset (Fin n) => 1 + (S.card : ℤ)) hSet

/-- Symmetry and binary entries turn the diagonal Gram entry into the row sum. -/
theorem symmetric_binary_square_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hSymm : C.IsSymm) (hBinary : ∀ i j, C i j = 0 ∨ C i j = 1) (i : ι) :
    (C * C) i i = ∑ j, C i j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hSymm.apply i j]
  rcases hBinary i j with h | h <;> simp [h]

end Erdos60Private
end


open Filter SimpleGraph Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- The parent-to-old Gram entry counts the old packing neighbors and the parent loop. -/
theorem packingCompletion_square_parent {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) (v : Fin n) :
    (packingCompletion q G P * packingCompletion q G P) none (some v) =
      (if v ∈ P then 1 else 0) + ((G.neighborFinset v ∩ P).card : ℤ) := by
  let D : Matrix (Fin n) (Fin n) ℤ := Matrix.diagonal (fun x : Fin n => if x ∈ lowVertices q G \ P then (1 : ℤ) else 0)
  have hLoop (w) : (if w ∈ P then (1 : ℤ) else 0) * D w v = 0 := by
    by_cases h : w = v
    · subst w
      by_cases hv : v ∈ P <;> simp [D, hv]
    · simp [D, h]
  have hTerm (w) : (if w ∈ P then (1 : ℤ) else 0) * (G.adjMatrix ℤ w v + D w v) =
      if w ∈ P then G.adjMatrix ℤ w v else 0 := by
    rw [mul_add, hLoop, add_zero]
    by_cases hw : w ∈ P <;> simp [hw]
  rw [Matrix.mul_apply, Fintype.sum_option]
  change (1 : ℤ) * (if v ∈ P then 1 else 0) +
    (∑ w, (if w ∈ P then 1 else 0) * (G.adjMatrix ℤ w v + D w v)) = _
  rw [one_mul, Finset.sum_congr rfl (fun w _ => hTerm w), ← Finset.sum_filter]
  have hSet : (Finset.univ.filter fun w => w ∈ P) = P := by ext w; simp
  rw [hSet]
  have hSum : (∑ w ∈ P, G.adjMatrix ℤ w v) = ((G.neighborFinset v ∩ P).card : ℤ) := by
    simpa only [G.adjMatrix_apply, G.adj_comm] using (neighbor_intersection_card_eq_sum_adjacency G P v).symm
  rw [hSum]

/-- Old off-diagonal Gram entries receive the parent contribution and the possible endpoint loops. -/
theorem packingCompletion_square_old {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Fin n))
    (v w : Fin n) (hvw : v ≠ w) :
    (packingCompletion q G P * packingCompletion q G P) (some v) (some w) =
      (if v ∈ P then (1 : ℤ) else 0) * (if w ∈ P then 1 else 0) +
      (G.adjMatrix ℤ * G.adjMatrix ℤ) v w +
      G.adjMatrix ℤ v w * (if w ∈ lowVertices q G \ P then 1 else 0) +
      (if v ∈ lowVertices q G \ P then 1 else 0) * G.adjMatrix ℤ v w := by
  rw [Matrix.mul_apply, Fintype.sum_option]
  change (if v ∈ P then (1 : ℤ) else 0) * (if w ∈ P then 1 else 0) +
    ((G.adjMatrix ℤ + Matrix.diagonal (fun x : Fin n => if x ∈ lowVertices q G \ P then (1 : ℤ) else 0)) *
      (G.adjMatrix ℤ + Matrix.diagonal (fun x : Fin n => if x ∈ lowVertices q G \ P then (1 : ℤ) else 0))) v w = _
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_apply, ite_eq_right hvw]
  ring

/-- The normalized packing data give at most one common incidence between distinct completed rows. -/
theorem packingCompletion_square_off_diagonal_le {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n))
    (hFree : (cycleGraph 4).Free G) (P : Finset (Fin n))
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hOutsideIndependent : ∀ v ∈ lowVertices q G \ P, ∀ w ∈ lowVertices q G \ P, ¬G.Adj v w)
    (hOutsideTriangle : ∀ v ∈ lowVertices q G \ P, ∀ w, G.Adj v w → codegree G v w = 0) :
    ∀ i j, i ≠ j → (packingCompletion q G P * packingCompletion q G P) i j ≤ 1 := by
  let C := packingCompletion q G P
  have hParent (v : Fin n) : (C * C) none (some v) ≤ 1 := by
    rw [packingCompletion_square_parent]
    by_cases hv : v ∈ P
    · have hEmpty : G.neighborFinset v ∩ P = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact hIndependent v hv w (Finset.mem_inter.mp hw).2 ((G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1)
      simp [hv, hEmpty]
    · rw [ite_eq_right hv, zero_add]
      exact_mod_cast open_packing_neighbor_card_le_one G P hOpen v
  have hOld (v w : Fin n) (hvw : v ≠ w) : (C * C) (some v) (some w) ≤ 1 := by
    rw [packingCompletion_square_old q G P v w hvw, adjMatrix_square_codegree]
    by_cases hBoth : v ∈ P ∧ w ∈ P
    · have hvX : v ∉ lowVertices q G \ P := fun h => (Finset.mem_sdiff.mp h).2 hBoth.1
      have hwX : w ∉ lowVertices q G \ P := fun h => (Finset.mem_sdiff.mp h).2 hBoth.2
      simp [hBoth.1, hBoth.2, hvX, hwX, hOpen v hBoth.1 w hBoth.2 hvw]
    · have hParentZero : (if v ∈ P then (1 : ℤ) else 0) * (if w ∈ P then 1 else 0) = 0 := by
        by_cases hv : v ∈ P <;> by_cases hw : w ∈ P <;> simp_all
      rw [hParentZero, zero_add]
      have hCodegree : (codegree G v w : ℤ) ≤ 1 := by exact_mod_cast codegree_le_one G hFree v w hvw
      by_cases hAdj : G.Adj v w
      · rw [G.adjMatrix_apply, ite_eq_left hAdj, one_mul, mul_one]
        by_cases hvX : v ∈ lowVertices q G \ P
        · have hwX : w ∉ lowVertices q G \ P := fun hw => hOutsideIndependent v hvX w hw hAdj
          have hZero := hOutsideTriangle v hvX w hAdj
          simp [hvX, hwX, hZero]
        · by_cases hwX : w ∈ lowVertices q G \ P
          · have hZero : codegree G v w = 0 := by
              rw [codegree_symm G v w]
              exact hOutsideTriangle w hwX v hAdj.symm
            simp [hvX, hwX, hZero]
          · simpa [hvX, hwX] using hCodegree
      · simp only [G.adjMatrix_apply, ite_eq_right hAdj, zero_mul, mul_zero, add_zero]
        exact hCodegree
  have hSymm : (C * C).IsSymm := by
    change (C * C)ᵀ = C * C
    rw [Matrix.transpose_mul, packingCompletion_symmetric q G P]
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some v => exact hParent v
  | some v =>
    cases j with
    | none =>
      rw [← hSymm.apply (some v) none]
      exact hParent v
    | some w =>
      exact hOld v w (fun h => hij (congrArg some h))

end Erdos60Private
end



open Filter SimpleGraph Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- The missing common incidences of a regular completed matrix. -/
def completionResidual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  (q : ℤ) • (1 : Matrix ι ι ℤ) + (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℤ)) - C * C

theorem completionResidual_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) (hSymm : C.IsSymm) :
    (completionResidual q C).IsSymm := by
  change (completionResidual q C)ᵀ = completionResidual q C
  simp only [completionResidual, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_mul, hSymm.eq]
  rfl

theorem completionResidual_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) (hSymm : C.IsSymm)
    (hBinary : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hRow : ∀ i, (∑ j, C i j) = (q : ℤ) + 1) (i : ι) :
    completionResidual q C i i = 0 := by
  have hDiag := symmetric_binary_square_diagonal C hSymm hBinary i
  rw [hRow] at hDiag
  change (q : ℤ) * (1 : Matrix ι ι ℤ) i i + 1 - (C * C) i i = 0
  rw [Matrix.one_apply_eq, mul_one, hDiag]
  ring

theorem completionResidual_binary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) (hSymm : C.IsSymm)
    (hBinary : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hRow : ∀ i, (∑ j, C i j) = (q : ℤ) + 1)
    (hGram : ∀ i j, i ≠ j → (C * C) i j ≤ 1) (i j : ι) :
    completionResidual q C i j = 0 ∨ completionResidual q C i j = 1 := by
  by_cases hij : i = j
  · subst j
    exact Or.inl (completionResidual_diagonal q C hSymm hBinary hRow i)
  · have hUpper := hGram i j hij
    have hLower : 0 ≤ (C * C) i j := by
      apply Finset.sum_nonneg
      intro k _
      rcases hBinary i k with h | h <;> rcases hBinary k j with h' | h' <;> simp [h, h']
    have hEntry : completionResidual q C i j = 1 - (C * C) i j := by
      change (q : ℤ) * (1 : Matrix ι ι ℤ) i j + 1 - (C * C) i j = _
      rw [Matrix.one_apply_ne hij, mul_zero, zero_add]
    omega

theorem completionResidual_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ)
    (hCard : Fintype.card ι = q ^ 2 + q + 3)
    (hRow : ∀ i, (∑ j, C i j) = (q : ℤ) + 1) (i : ι) :
    (∑ j, completionResidual q C i j) = 2 := by
  have hSquare : (∑ j, (C * C) i j) = ((q : ℤ) + 1) ^ 2 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hRow, ← Finset.sum_mul]
    ring
  have hNat : (Fintype.card ι : ℤ) = (q : ℤ) ^ 2 + q + 3 := by exact_mod_cast hCard
  simp only [completionResidual, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    mul_one, Finset.sum_const, nsmul_eq_mul]
  rw [hSquare]
  simp only [Finset.card_univ]
  nlinarith only [hNat]

theorem regular_matrix_mul_ones {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℤ) (r : ℤ) (hRow : ∀ i, (∑ j, C i j) = r) :
    C * (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℤ)) =
      r • (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℤ)) := by
  ext i j
  simpa only [Matrix.mul_apply, Matrix.of_apply, mul_one, Matrix.smul_apply, smul_eq_mul] using hRow i

theorem symmetric_regular_ones_mul {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℤ) (r : ℤ) (hSymm : C.IsSymm)
    (hRow : ∀ i, (∑ j, C i j) = r) :
    (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℤ)) * C =
      r • (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℤ)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, one_mul, Matrix.smul_apply, smul_eq_mul, mul_one]
  calc
    (∑ k, C k j) = ∑ k, C j k := Finset.sum_congr rfl (fun k _ => hSymm.apply j k)
    _ = r := hRow j

theorem completionResidual_commutes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) (hSymm : C.IsSymm)
    (hRow : ∀ i, (∑ j, C i j) = (q : ℤ) + 1) :
    C * completionResidual q C = completionResidual q C * C := by
  simp only [completionResidual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    regular_matrix_mul_ones C _ hRow, symmetric_regular_ones_mul C _ hSymm hRow,
    Matrix.mul_assoc]

/-- The residual matrix gives a loopless graph with exactly two neighbors per vertex. -/
def completionResidualGraph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ completionResidual q C i j = 1 ∧ completionResidual q C j i = 1
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem completionResidualGraph_adjMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) (hSymm : C.IsSymm)
    (hBinary : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hRow : ∀ i, (∑ j, C i j) = (q : ℤ) + 1)
    (hGram : ∀ i j, i ≠ j → (C * C) i j ≤ 1) :
    (completionResidualGraph q C).adjMatrix ℤ = completionResidual q C := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  have hZSymm := completionResidual_symmetric q C hSymm
  rcases completionResidual_binary q C hSymm hBinary hRow hGram i j with hZero | hOne
  · have hNot : ¬(completionResidualGraph q C).Adj i j := by
      intro h
      have hBad : completionResidual q C i j = 1 := h.2.1
      omega
    simp [hNot, hZero]
  · have hij : i ≠ j := by
      intro h
      subst j
      have hDiag := completionResidual_diagonal q C hSymm hBinary hRow i
      omega
    have hAdj : (completionResidualGraph q C).Adj i j :=
      ⟨hij, hOne, by rw [hZSymm.apply i j]; exact hOne⟩
    simp [hAdj, hOne]

theorem completionResidualGraph_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) (hSymm : C.IsSymm)
    (hBinary : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hCard : Fintype.card ι = q ^ 2 + q + 3)
    (hRow : ∀ i, (∑ j, C i j) = (q : ℤ) + 1)
    (hGram : ∀ i j, i ≠ j → (C * C) i j ≤ 1) (i : ι) :
    (completionResidualGraph q C).degree i = 2 := by
  let G := completionResidualGraph q C
  have hDegree : (∑ j, G.adjMatrix ℤ i j) = (G.degree i : ℤ) := by
    simpa only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] using
      (SimpleGraph.adjMatrix_mulVec_const_apply (G := G) (a := (1 : ℤ)) (v := i))
  rw [completionResidualGraph_adjMatrix q C hSymm hBinary hRow hGram] at hDegree
  have hSum := completionResidual_row_sum q C hCard hRow i
  have hResult : (G.degree i : ℤ) = 2 := by linarith only [hDegree, hSum]
  exact_mod_cast hResult

theorem packingCompletion_trace_of_excess (q a : ℕ)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (P : Finset (Fin (q ^ 2 + q + 2)))
    (hEdges : G.edgeFinset.card = planeEdgeCount q + a)
    (hCard : P.card = q) (hLow : P ⊆ lowVertices q G)
    (hUnit : ∀ v, signedDeficiency q G v = 0 ∨ signedDeficiency q G v = 1) :
    (packingCompletion q G P).trace = (q : ℤ) + 3 - 2 * a := by
  have hEach (v : Fin (q ^ 2 + q + 2)) :
      signedDeficiency q G v = if v ∈ lowVertices q G then 1 else 0 := by
    rcases hUnit v with h | h <;> simp [lowVertices, h]
  have hTotal := signedDeficiency_sum_of_excess q a G hEdges
  simp only [hEach] at hTotal
  have hLowCard : ((lowVertices q G).card : ℤ) = 2 * q + 2 - 2 * a := by
    simpa using hTotal
  have hSplit := Finset.card_sdiff_add_card_eq_card hLow
  have hSplitInt : ((lowVertices q G \ P).card : ℤ) + q = (lowVertices q G).card := by
    simpa only [hCard, Nat.cast_add, Nat.cast_ofNat] using congrArg (fun n : ℕ => (n : ℤ)) hSplit
  rw [packingCompletion_trace]
  omega

end Erdos60Private

end


open Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- A rational matrix whose square is a positive nonsquare scalar has zero trace. -/
theorem rational_scalar_square_trace_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℚ) (a : ℚ) (ha : 0 < a) (hNotSquare : ¬IsSquare a)
    (hSquare : C * C = a • (1 : Matrix ι ι ℚ)) : C.trace = 0 := by
  let f : Matrix ι ι ℚ →+* Matrix ι ι ℝ := (algebraMap ℚ ℝ).mapMatrix
  let B := f C
  let s := Real.sqrt (a : ℝ)
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  have hs : 0 < s := Real.sqrt_pos.2 haReal
  have hsSquare : s ^ 2 = (a : ℝ) := Real.sq_sqrt haReal.le
  have hScalar : f (a • (1 : Matrix ι ι ℚ)) = (a : ℝ) • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [f, hij]
  have hB : B * B = (a : ℝ) • (1 : Matrix ι ι ℝ) := by
    simpa only [map_mul, hScalar] using congrArg f hSquare
  have hBTrace : B.trace = (C.trace : ℝ) := by
    simp [B, f, Matrix.trace]
  let D := s⁻¹ • B
  have hD : D * D = 1 := by
    dsimp only [D]
    rw [smul_mul_assoc, mul_smul_comm, hB, smul_smul, smul_smul]
    have hCoef : s⁻¹ * s⁻¹ * (a : ℝ) = 1 := by
      rw [← hsSquare]
      field_simp
    rw [hCoef, one_smul]
  let P := (1 / 2 : ℝ) • (1 + D)
  have hP : P * P = P := by
    dsimp only [P]
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hD]
    ext i j
    dsimp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  let e : Matrix ι ι ℝ ≃ₐ[ℝ] Module.End ℝ (ι → ℝ) := Matrix.toLinAlgEquiv'
  let PL := e P
  have hPL : PL * PL = PL := by
    simpa only [map_mul] using congrArg e hP
  let d := Module.finrank ℝ (LinearMap.range PL)
  have hRank : P.trace = (d : ℝ) := by
    have h := (LinearMap.IsIdempotentElem.isProj_range PL
      (show IsIdempotentElem PL from hPL)).trace
    change LinearMap.trace ℝ (ι → ℝ) P.toLin' = (d : ℝ) at h
    simpa only [Matrix.trace_toLin'_eq] using h
  have hTrace : (C.trace : ℝ) = (2 * (d : ℝ) - Fintype.card ι) * s := by
    have h := hRank
    dsimp only [P, D] at h
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Matrix.trace_smul, hBTrace] at h
    simp only [smul_eq_mul] at h
    have hInv : s * s⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hs)
    have hScaled := congrArg (fun x : ℝ => (2 * s) * x) h
    have hCancel : s * (s⁻¹ * (C.trace : ℝ)) = (C.trace : ℝ) := by rw [← mul_assoc, hInv, one_mul]
    nlinarith only [hScaled, hCancel]
  let t : ℚ := 2 * d - Fintype.card ι
  have htCast : (t : ℝ) = 2 * (d : ℝ) - Fintype.card ι := by simp [t]
  by_cases ht : t = 0
  · rw [← htCast, ht, Rat.cast_zero, zero_mul] at hTrace
    exact_mod_cast hTrace
  · have htReal : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have hRatio : ((C.trace / t : ℚ) : ℝ) = s := by
      rw [Rat.cast_div, div_eq_iff htReal, hTrace, htCast]
      ring
    have hRationalSquare : (C.trace / t) ^ 2 = a := by
      apply Rat.cast_injective (α := ℝ)
      rw [Rat.cast_pow]
      rw [hRatio, hsSquare]
    exact False.elim (hNotSquare ((isSquare_iff_exists_sq a).mpr ⟨C.trace / t, hRationalSquare.symm⟩))

theorem rational_endomorphism_scalar_square_trace_zero {V : Type*} [AddCommGroup V]
    [Module ℚ V] [FiniteDimensional ℚ V] (T : Module.End ℚ V) (a : ℚ)
    (ha : 0 < a) (hNotSquare : ¬IsSquare a)
    (hSquare : T * T = a • (1 : Module.End ℚ V)) : LinearMap.trace ℚ V T = 0 := by
  let b := Module.finBasis ℚ V
  have hMatrix : (LinearMap.toMatrix b b T) * (LinearMap.toMatrix b b T) =
      a • (1 : Matrix (Fin (Module.finrank ℚ V)) (Fin (Module.finrank ℚ V)) ℚ) := by
    simpa only [LinearMap.toMatrix_mul, map_smul, LinearMap.toMatrix_one] using
      congrArg (LinearMap.toMatrix b b) hSquare
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  exact rational_scalar_square_trace_zero _ a ha hNotSquare hMatrix

/-- The trace on a commuting rational projection vanishes under a nonsquare scalar square. -/
theorem rational_projected_scalar_square_trace_zero {V : Type*} [AddCommGroup V]
    [Module ℚ V] [FiniteDimensional ℚ V] (B P : Module.End ℚ V) (a : ℚ)
    (ha : 0 < a) (hNotSquare : ¬IsSquare a)
    (hIdem : P * P = P) (hComm : B * P = P * B)
    (hSquare : B * B * P = a • P) : LinearMap.trace ℚ V (B * P) = 0 := by
  let S := LinearMap.range P
  have hProj := LinearMap.IsIdempotentElem.isProj_range P (show IsIdempotentElem P from hIdem)
  have hInvariant (x : V) (hx : x ∈ S) : B x ∈ S := by
    apply hProj.mem_iff_map_id.mpr
    calc
      P (B x) = B (P x) := (congrArg (fun f : Module.End ℚ V => f x) hComm).symm
      _ = B x := by rw [hProj.map_id x hx]
  let T : Module.End ℚ S := B.restrict hInvariant
  have hTSquare : T * T = a • (1 : Module.End ℚ S) := by
    ext x
    change B (B (x : V)) = a • (x : V)
    have h := congrArg (fun f : Module.End ℚ V => f (x : V)) hSquare
    change B (B (P (x : V))) = a • P (x : V) at h
    simpa only [hProj.map_id (x : V) x.property] using h
  have hFactor : (B.comp S.subtype).comp P.rangeRestrict = B * P := by
    ext x
    rfl
  have hRestrict : P.rangeRestrict.comp (B.comp S.subtype) = T := by
    ext x
    change P (B (x : V)) = B (x : V)
    exact hProj.map_id _ (hInvariant _ x.property)
  rw [← hFactor, LinearMap.trace_comp_comm', hRestrict]
  exact rational_endomorphism_scalar_square_trace_zero T a ha hNotSquare hTSquare

theorem rational_matrix_projected_scalar_square_trace_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B P : Matrix ι ι ℚ) (a : ℚ)
    (ha : 0 < a) (hNotSquare : ¬IsSquare a)
    (hIdem : P * P = P) (hComm : B * P = P * B)
    (hSquare : B * B * P = a • P) : (B * P).trace = 0 := by
  let e : Matrix ι ι ℚ ≃ₐ[ℚ] Module.End ℚ (ι → ℚ) := Matrix.toLinAlgEquiv'
  have hIdemL : e P * e P = e P := by simpa only [map_mul] using congrArg e hIdem
  have hCommL : e B * e P = e P * e B := by simpa only [map_mul] using congrArg e hComm
  have hSquareL : e B * e B * e P = a • e P := by
    simpa only [map_mul, map_smul] using congrArg e hSquare
  have h := rational_projected_scalar_square_trace_zero (e B) (e P) a ha hNotSquare
    hIdemL hCommL hSquareL
  change LinearMap.trace ℚ (ι → ℚ) (e B * e P) = 0 at h
  rw [← map_mul] at h
  exact (Matrix.trace_toLin'_eq (B * P)).symm.trans h

end Erdos60Private

end


open Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- Two binary cyclic arrays with equal successive differences agree if one varies. -/
theorem cyclic_binary_same_differences {s : ℕ} [NeZero s]
    (a b : ZMod s → ℤ)
    (ha : ∀ i, a i = 0 ∨ a i = 1) (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hStep : ∀ i, b i + a (i + 1) = a i + b (i + 1))
    (hVaries : ∃ x y, b x ≠ b y) : ∀ i, a i = b i := by
  have hNat (k : ℕ) : a (k : ZMod s) - b (k : ZMod s) = a 0 - b 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hStep (k : ZMod s)
      simp only [Nat.cast_add, Nat.cast_one] at ⊢
      omega
  have hConst (i : ZMod s) : a i - b i = a 0 - b 0 := by
    simpa using hNat i.val
  obtain ⟨x, y, hxy⟩ := hVaries
  intro i
  have hx := hConst x
  have hy := hConst y
  have hi := hConst i
  have hax := ha x
  have hay := ha y
  have hai := ha i
  have hbx := hb x
  have hby := hb y
  have hbi := hb i
  omega

/-- Commutation with the cycle adjacency advances a varying binary diagonal by two. -/
theorem cyclic_binary_next_diagonal {s : ℕ} [NeZero s]
    (A : Matrix (ZMod s) (ZMod s) ℤ)
    (hBinary : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hComm : ∀ i j, A i (j - 1) + A i (j + 1) = A (i - 1) j + A (i + 1) j)
    (d : ZMod s) (hVaries : ∃ x y, A x (x + d) ≠ A y (y + d)) :
    ∀ i, A i (i + d + 2) = A (i + 1) (i + 1 + d) := by
  let a : ZMod s → ℤ := fun i => A i (i + d + 2)
  let b : ZMod s → ℤ := fun i => A (i + 1) (i + 1 + d)
  have hStep (i : ZMod s) : b i + a (i + 1) = a i + b (i + 1) := by
    dsimp only [a, b]
    convert hComm (i + 1) (i + d + 2) using 1 <;> congr 1 <;> ring
  have hVaries' : ∃ x y, b x ≠ b y := by
    obtain ⟨x, y, hxy⟩ := hVaries
    refine ⟨x - 1, y - 1, ?_⟩
    simpa only [b, sub_add_cancel] using hxy
  exact cyclic_binary_same_differences a b (fun i => hBinary _ _) (fun i => hBinary _ _) hStep hVaries'

/-- Every odd cyclic diagonal is a translate of a nonconstant first diagonal. -/
theorem cyclic_binary_odd_diagonal {s : ℕ} [NeZero s]
    (A : Matrix (ZMod s) (ZMod s) ℤ)
    (hBinary : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hComm : ∀ i j, A i (j - 1) + A i (j + 1) = A (i - 1) j + A (i + 1) j)
    (hVaries : ∃ x y, A x (x + 1) ≠ A y (y + 1)) :
    ∀ k : ℕ, ∀ i, A i (i + (2 * (k : ZMod s) + 1)) = A (i + k) (i + k + 1) := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
    have hVariesK : ∃ x y,
        A x (x + (2 * (k : ZMod s) + 1)) ≠ A y (y + (2 * (k : ZMod s) + 1)) := by
      obtain ⟨x, y, hxy⟩ := hVaries
      refine ⟨x - k, y - k, ?_⟩
      simpa only [ih, sub_add_cancel] using hxy
    intro i
    have hNext := cyclic_binary_next_diagonal A hBinary hComm (2 * (k : ZMod s) + 1) hVariesK i
    rw [ih] at hNext
    convert hNext using 1 <;> push_cast <;> congr 1 <;> ring

/-- A transition of binary values is bounded by the two endpoint values. -/
theorem binary_transition_indicator_le (x y : ℤ) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    (if x ≠ y then (1 : ℤ) else 0) ≤ x + y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

/-- Recording the quotient makes doubling on a finite cyclic group injective. -/
def cyclicDoubleLift {s : ℕ} [NeZero s] (j : ZMod s) : ZMod s × Fin 2 :=
  (2 * j + 1, ⟨(2 * j.val + 1) / s, by
    apply (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne s))).mpr
    have hj := j.val_lt
    omega⟩)

theorem cyclicDoubleLift_injective {s : ℕ} [NeZero s] :
    Function.Injective (cyclicDoubleLift (s := s)) := by
  have hVal (j : ZMod s) : (2 * j + 1).val = (2 * j.val + 1) % s := by
    have hCast : ((2 * j.val + 1 : ℕ) : ZMod s) = 2 * j + 1 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [← hCast, ZMod.val_natCast]
  intro x y hxy
  have hFirst := congrArg (fun p : ZMod s × Fin 2 => p.1.val) hxy
  have hSecond := congrArg (fun p : ZMod s × Fin 2 => p.2.val) hxy
  change (2 * x + 1).val = (2 * y + 1).val at hFirst
  change (2 * x.val + 1) / s = (2 * y.val + 1) / s at hSecond
  rw [hVal, hVal] at hFirst
  have hx := Nat.mod_add_div (2 * x.val + 1) s
  have hy := Nat.mod_add_div (2 * y.val + 1) s
  rw [hFirst, hSecond] at hx
  apply ZMod.val_injective s
  omega

/-- A doubled cyclic index uses each entry at most twice. -/
theorem cyclic_double_sum_le {s : ℕ} [NeZero s] (g : ZMod s → ℤ)
    (hNonneg : ∀ i, 0 ≤ g i) :
    (∑ j, g (2 * j + 1)) ≤ 2 * ∑ j, g j := by
  have hSum : (∑ j, g (2 * j + 1)) ≤ ∑ p : ZMod s × Fin 2, g p.1 := by
    apply Finset.sum_le_sum_of_injOn cyclicDoubleLift cyclicDoubleLift_injective.injOn
      (Finset.subset_univ _)
    · intro i _
      rfl
    · intro p _ _
      exact hNonneg p.1
  simpa only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib, two_mul] using hSum

/-- A binary matrix commuting with a cycle has at most four row-sums of first-diagonal transitions. -/
theorem cyclic_binary_transition_bound {s : ℕ} [NeZero s]
    (A : Matrix (ZMod s) (ZMod s) ℤ)
    (hBinary : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hComm : ∀ i j, A i (j - 1) + A i (j + 1) = A (i - 1) j + A (i + 1) j) :
    (∑ i, if A i (i + 1) ≠ A (i - 1) i then (1 : ℤ) else 0) ≤
      4 * ∑ j, A 0 j := by
  let u : ZMod s → ℤ := fun i => A i (i + 1)
  have hNonneg (i j : ZMod s) : 0 ≤ A i j := by rcases hBinary i j with h | h <;> omega
  by_cases hVaries : ∃ x y, A x (x + 1) ≠ A y (y + 1)
  · have hOddSum : (∑ j : ZMod s, A 0 (2 * j + 1)) = ∑ j, u j := by
      apply Finset.sum_congr rfl
      intro j _
      have h := cyclic_binary_odd_diagonal A hBinary hComm hVaries j.val 0
      simpa [u] using h
    have hDoubled := cyclic_double_sum_le (fun j => A 0 j) (hNonneg 0)
    rw [hOddSum] at hDoubled
    have hTransitions : (∑ i, if A i (i + 1) ≠ A (i - 1) i then (1 : ℤ) else 0) ≤
        ∑ i, (u i + u (i - 1)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [u] using binary_transition_indicator_le (u i) (u (i - 1))
        (hBinary i (i + 1)) (hBinary (i - 1) (i - 1 + 1))
    have hShift : (∑ i, u (i - 1)) = ∑ i, u i := by
      simpa [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-1 : ZMod s)) u
    rw [Finset.sum_add_distrib, hShift] at hTransitions
    omega
  · have hSame (i : ZMod s) : A i (i + 1) = A (i - 1) i := by
      have h : A i (i + 1) = A (i - 1) (i - 1 + 1) := by
        by_contra h
        exact hVaries ⟨i, i - 1, h⟩
      simpa using h
    simp only [hSame, ne_eq, not_true_eq_false, ite_false, Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => hNonneg 0 j))

/-- A rational harmonic function on a finite cycle is constant. -/
theorem cyclic_harmonic_constant {s : ℕ} [NeZero s] (f : ZMod s → ℚ)
    (hHarmonic : ∀ i, 2 * f i = f (i - 1) + f (i + 1)) :
    ∀ i, f i = f 0 := by
  let g : ZMod s → ℚ := fun i => f (i + 1) - f i
  have hStep (i : ZMod s) : g (i + 1) = g i := by
    have h := hHarmonic (i + 1)
    have hCancel : i + 1 - 1 = i := by ring
    rw [hCancel] at h
    dsimp only [g]
    linarith
  have hNat (k : ℕ) : g (k : ZMod s) = g 0 := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.cast_add, Nat.cast_one] using (hStep (k : ZMod s)).trans ih
  have hConst (i : ZMod s) : g i = g 0 := by simpa using hNat i.val
  have hSum : (∑ i, g i) = 0 := by
    simp only [g, Finset.sum_sub_distrib]
    have hShift := Equiv.sum_comp (Equiv.addRight (1 : ZMod s)) f
    simpa using sub_eq_zero.mpr hShift
  have hProduct : (s : ℚ) * g 0 = 0 := by
    simpa only [hConst, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card] using hSum
  have hZero : g 0 = 0 := (mul_eq_zero.mp hProduct).resolve_left (by exact_mod_cast NeZero.ne s)
  have hFStep (i : ZMod s) : f (i + 1) = f i := by
    have h := (hConst i).trans hZero
    dsimp only [g] at h
    linarith
  have hFNat (k : ℕ) : f (k : ZMod s) = f 0 := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.cast_add, Nat.cast_one] using (hFStep (k : ZMod s)).trans ih
  intro i
  simpa using hFNat i.val

end Erdos60Private

end


open SimpleGraph
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


def cycleVertex {V : Type*} {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (i : ZMod p.length) : V := p.getVert i.val

theorem cycleVertex_injective {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) [NeZero p.length] :
    Function.Injective (cycleVertex p) := by
  intro i j hij
  apply ZMod.val_injective p.length
  apply hp.getVert_injOn' (by have h := i.val_lt; simp only [Set.mem_ofPred_eq]; omega)
    (by have h := j.val_lt; simp only [Set.mem_ofPred_eq]; omega)
  exact hij

theorem cycleVertex_mem_support {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (i : ZMod p.length) : cycleVertex p i ∈ p.support :=
  p.getVert_mem_support i.val

theorem cycleVertex_surjective_support {V : Type*} {G : SimpleGraph V} {v w : V}
    (p : G.Walk v v) [NeZero p.length] (hw : w ∈ p.support) :
    ∃ i : ZMod p.length, cycleVertex p i = w := by
  obtain ⟨k, hk, hkl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  by_cases hlt : k < p.length
  · refine ⟨k, ?_⟩
    simpa only [cycleVertex, ZMod.val_natCast_of_lt hlt] using hk
  · have heq : k = p.length := by omega
    refine ⟨0, ?_⟩
    simpa only [heq, p.getVert_length, cycleVertex, ZMod.val_zero, p.getVert_zero] using hk

theorem cycleVertex_adj_next {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (_hp : p.IsCycle) [NeZero p.length] (i : ZMod p.length) :
    G.Adj (cycleVertex p i) (cycleVertex p (i + 1)) := by
  have hAdj := p.adj_getVert_succ i.val_lt
  have hCast : ((i.val + 1 : ℕ) : ZMod p.length) = i + 1 := by simp
  have hVal : (i + 1).val = (i.val + 1) % p.length := by rw [← hCast, ZMod.val_natCast]
  by_cases hlt : i.val + 1 < p.length
  · simpa only [cycleVertex, hVal, Nat.mod_eq_of_lt hlt] using hAdj
  · have heq : i.val + 1 = p.length := by have h := i.val_lt; omega
    simpa only [heq, p.getVert_length, cycleVertex, hVal, Nat.mod_self, p.getVert_zero] using hAdj

theorem cycleVertex_prev_ne_next {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) [NeZero p.length] (i : ZMod p.length) :
    cycleVertex p (i - 1) ≠ cycleVertex p (i + 1) := by
  intro h
  have hi := cycleVertex_injective p hp h
  have hTwo : (2 : ZMod p.length) = 0 := by linear_combination -hi
  have hVal : (2 : ZMod p.length).val = 2 :=
    ZMod.val_natCast_of_lt (n := p.length) (a := 2) (by have h := hp.three_le_length; omega)
  have hBad := congrArg ZMod.val hTwo
  rw [hVal, ZMod.val_zero] at hBad
  omega

theorem cycleVertex_neighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hDegree : ∀ v, G.degree v = 2) {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) [NeZero p.length] (i : ZMod p.length) :
    G.neighborFinset (cycleVertex p i) = {cycleVertex p (i - 1), cycleVertex p (i + 1)} := by
  have hPrev : G.Adj (cycleVertex p i) (cycleVertex p (i - 1)) := by
    have h := (cycleVertex_adj_next p hp (i - 1)).symm
    simpa only [sub_add_cancel] using h
  have hNext := cycleVertex_adj_next p hp i
  have hSubset : {cycleVertex p (i - 1), cycleVertex p (i + 1)} ⊆ G.neighborFinset (cycleVertex p i) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hPrev
    · exact (G.mem_neighborFinset _ _).mpr hNext
  apply (Finset.eq_of_subset_of_card_le hSubset ?_).symm
  rw [Finset.card_pair (cycleVertex_prev_ne_next p hp i), G.card_neighborFinset_eq_degree, hDegree]

/-- Each connected component of a finite degree-two graph has cyclic coordinates. -/
theorem degree_two_component_cyclic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hDegree : ∀ v, G.degree v = 2) (c : G.ConnectedComponent) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ e : ZMod s ≃ c.supp,
      ∀ i, G.neighborFinset (e i).val = {(e (i - 1)).val, (e (i + 1)).val} := by
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hCycles : G.IsCycles := by
    intro w _
    rw [G.ncard_neighborSet, hDegree]
  have hNeighbors : (G.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [G.ncard_neighborSet, hDegree]
    norm_num
  obtain ⟨p, hp, hpc⟩ := hCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hNeighbors
  let : NeZero p.length := ⟨by have h := hp.three_le_length; omega⟩
  let f : ZMod p.length → c.supp := fun i => ⟨cycleVertex p i, by
    rw [← hpc]
    exact p.mem_verts_toSubgraph.mpr (cycleVertex_mem_support p i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact cycleVertex_injective p hp (congrArg Subtype.val hij)
    · intro w
      have hw : w.val ∈ p.support := by
        apply p.mem_verts_toSubgraph.mp
        rw [hpc]
        exact w.property
      obtain ⟨i, hi⟩ := cycleVertex_surjective_support p hw
      exact ⟨i, Subtype.ext hi⟩
  refine ⟨p.length, hp.three_le_length, Equiv.ofBijective f hf, ?_⟩
  intro i
  exact cycleVertex_neighborFinset G hDegree p hp i

/-- Cyclic coordinates on all connected components give coordinates on the whole graph. -/
theorem degree_two_cyclic_coordinates {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hDegree : ∀ v, G.degree v = 2) :
    ∃ s : G.ConnectedComponent → ℕ, (∀ c, 3 ≤ s c) ∧
      ∃ e : (Σ c, ZMod (s c)) ≃ V,
        ∀ c i, G.neighborFinset (e ⟨c, i⟩) = {e ⟨c, i - 1⟩, e ⟨c, i + 1⟩} := by
  choose s hs e he using degree_two_component_cyclic G hDegree
  let f : (Σ c, ZMod (s c)) → V := fun x => (e x.1 x.2).val
  have hComp (c : G.ConnectedComponent) (i : ZMod (s c)) : G.connectedComponentMk (f ⟨c, i⟩) = c :=
    (e c i).property
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ hij
      have hcd : c = d := (hComp c i).symm.trans ((congrArg G.connectedComponentMk hij).trans (hComp d j))
      subst d
      have hi : i = j := (e c).injective (Subtype.ext hij)
      subst j
      rfl
    · intro v
      let c := G.connectedComponentMk v
      obtain ⟨i, hi⟩ := (e c).surjective ⟨v, rfl⟩
      exact ⟨⟨c, i⟩, congrArg Subtype.val hi⟩
  refine ⟨s, hs, Equiv.ofBijective f hf, ?_⟩
  intro c i
  exact he c i

end Erdos60Private

end


open Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- In characteristic two, the off-diagonal terms of a symmetric quadratic form cancel. -/
theorem symmetric_quadratic_mod_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 2)) (hSymm : M.IsSymm) (x : ι → ZMod 2) :
    (∑ j, ∑ k, x j * M j k * x k) = ∑ j, x j * M j j * x j := by
  let f : ι × ι → ZMod 2 := fun p => x p.1 * M p.1 p.2 * x p.2
  let S : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hOff : ∑ p ∈ S, f p = 0 := by
    apply Finset.sum_involution (fun p _ => Prod.swap p)
    · intro p _
      dsimp only [f, Prod.swap]
      rw [hSymm.apply p.1 p.2]
      ring_nf
      simp only [show (2 : ZMod 2) = 0 by decide, mul_zero]
    · intro p hp _ hEq
      have hNe := (Finset.mem_filter.mp hp).2
      exact hNe (congrArg Prod.snd hEq)
    · intro p hp
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap, ne_eq, eq_comm] using
        (Finset.mem_filter.mp hp).2
    · intro p _
      exact Prod.swap_swap p
  have hSplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (ι × ι)))
    (fun p => p.1 = p.2) f
  change (∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 = p.2), f p) + (∑ p ∈ S, f p) = ∑ p, f p at hSplit
  rw [hOff, add_zero] at hSplit
  calc
    (∑ j, ∑ k, x j * M j k * x k) = ∑ p, f p := by simp only [Fintype.sum_prod_type, f]
    _ = ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 = p.2), f p := hSplit.symm
    _ = ∑ j, x j * M j j * x j := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      simp [f]

theorem symmetric_binary_cube_mod_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℤ) (hSymm : C.IsSymm)
    (hBinary : ∀ i j, C i j = 0 ∨ C i j = 1) (i : ι) :
    (((C * C * C) i i : ℤ) : ZMod 2) = ∑ j, (C i j : ZMod 2) * (C j j : ZMod 2) := by
  let B : Matrix ι ι (ZMod 2) := fun i j => (C i j : ZMod 2)
  have hBSymm : B.IsSymm := by
    ext j k
    exact congrArg (fun z : ℤ => (z : ZMod 2)) (hSymm.apply j k)
  have hCube : (((C * C * C) i i : ℤ) : ZMod 2) = ∑ j, ∑ k, B i j * B j k * B i k := by
    simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [B]
    rw [hSymm.apply i k]
  rw [hCube, symmetric_quadratic_mod_two B hBSymm (fun j => B i j)]
  apply Finset.sum_congr rfl
  intro j _
  rcases hBinary i j with h | h <;> simp [B, h]

/-- A row incident to no loop has an odd number of incidences with its residual neighbors. -/
theorem loop_free_row_residual_odd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : Matrix ι ι ℤ) (hSymm : C.IsSymm)
    (hBinary : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hRow : ∀ i, (∑ j, C i j) = (q : ℤ) + 1)
    (hEven : Even q) (i : ι) (hNoLoop : ∀ j, C i j = 0 ∨ C j j = 0) :
    (((C * completionResidual q C) i i : ℤ) : ZMod 2) = 1 := by
  have hDiag : C i i = 0 := (hNoLoop i).elim id id
  have hCube := symmetric_binary_cube_mod_two C hSymm hBinary i
  have hCubeZero : (((C * C * C) i i : ℤ) : ZMod 2) = 0 := by
    rw [hCube]
    apply Finset.sum_eq_zero
    intro j _
    rcases hNoLoop j with h | h <;> simp [h]
  have hIdentity : (C * completionResidual q C) i i = (q : ℤ) + 1 - (C * C * C) i i := by
    simp only [completionResidual, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
      regular_matrix_mul_ones C _ hRow, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, hDiag, mul_zero, mul_one, zero_add,
      Matrix.mul_assoc]
  obtain ⟨k, hk⟩ := hEven
  have hqCast : ((q : ℤ) : ZMod 2) = 0 := by
    rw [hk]
    push_cast
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero]
  rw [hIdentity]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_one, hqCast, hCubeZero, zero_add]
  decide

end Erdos60Private

end


open Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- The trace on the cycle-constant subspace is forced by the completion identity. -/
theorem completion_cycle_projection_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (hq : 2 < q) (hNotSquare : ¬IsSquare ((q : ℚ) - 2))
    (C Z E : Matrix ι ι ℚ)
    (hCard : Fintype.card ι = q ^ 2 + q + 3)
    (hSquare : C * C = (q : ℚ) • 1 + (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)) - Z)
    (hRows : C * (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)) =
      ((q : ℚ) + 1) • (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)))
    (hCols : (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)) * C =
      ((q : ℚ) + 1) • (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)))
    (hIdem : E * E = E) (hComm : C * E = E * C)
    (hJE : (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)) * E =
      (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)))
    (hEJ : E * (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)) =
      (Matrix.of fun (_ : ι) (_ : ι) => (1 : ℚ)))
    (hZE : Z * E = (2 : ℚ) • E) : (C * E).trace = (q : ℚ) + 1 := by
  let J : Matrix ι ι ℚ := Matrix.of fun (_ : ι) (_ : ι) => 1
  let n : ℚ := Fintype.card ι
  have hn : n ≠ 0 := by dsimp only [n]; rw [hCard]; positivity
  have hnq : n = (q : ℚ) ^ 2 + q + 3 := by dsimp only [n]; exact_mod_cast hCard
  have hJJ : J * J = n • J := by ext i j; simp [J, n, Matrix.mul_apply]
  have hTraceJ : J.trace = n := by simp [J, n, Matrix.trace]
  let P := n⁻¹ • J
  have hPP : P * P = P := by
    dsimp only [P]
    rw [smul_mul_assoc, mul_smul_comm, hJJ, smul_smul, smul_smul]
    congr 1
    field_simp
  have hEP : E * P = P := by dsimp only [P, J]; rw [mul_smul_comm, hEJ]
  have hPE : P * E = P := by dsimp only [P, J]; rw [smul_mul_assoc, hJE]
  have hCP : C * P = ((q : ℚ) + 1) • P := by
    dsimp only [P, J]
    rw [mul_smul_comm, hRows, smul_smul, smul_smul]
    congr 1
    ring
  have hPC : P * C = ((q : ℚ) + 1) • P := by
    dsimp only [P, J]
    rw [smul_mul_assoc, hCols, smul_smul, smul_smul]
    congr 1
    ring
  have hTraceP : P.trace = 1 := by
    dsimp only [P]
    rw [Matrix.trace_smul, hTraceJ, smul_eq_mul, inv_mul_cancel₀ hn]
  let F := E - P
  have hFF : F * F = F := by
    dsimp only [F]
    rw [sub_mul, mul_sub, mul_sub, hIdem, hEP, hPE, hPP]
    abel
  have hCF : C * F = F * C := by
    dsimp only [F]
    rw [mul_sub, sub_mul, hComm, hCP, hPC]
  have hCCE : C * C * E = ((q : ℚ) - 2) • E + J := by
    rw [hSquare, sub_mul, add_mul, smul_mul_assoc, one_mul, hJE, hZE]
    change (q : ℚ) • E + J - (2 : ℚ) • E = _
    ext i j
    dsimp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hCCP : C * C * P = (((q : ℚ) + 1) ^ 2) • P := by
    rw [mul_assoc, hCP, mul_smul_comm, hCP, smul_smul]
    congr 1
    ring
  have hJP : J = n • P := by dsimp only [P]; rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hCCF : C * C * F = ((q : ℚ) - 2) • F := by
    dsimp only [F]
    rw [mul_sub, hCCE, hCCP, hJP, hnq]
    ext i j
    dsimp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hPositive : (0 : ℚ) < (q : ℚ) - 2 := by
    have hqRat : (2 : ℚ) < q := by exact_mod_cast hq
    linarith
  have hTraceF := rational_matrix_projected_scalar_square_trace_zero C F ((q : ℚ) - 2)
    hPositive hNotSquare hFF hCF hCCF
  dsimp only [F] at hTraceF
  rw [mul_sub, Matrix.trace_sub, hCP, Matrix.trace_smul, hTraceP, smul_eq_mul, mul_one] at hTraceF
  linarith

end Erdos60Private

end


open Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


section
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (s : κ → ℕ) [∀ c, NeZero (s c)]

/-- Orthogonal averaging on each cyclic block. -/
def cycleAverage : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) ℚ :=
  fun x y => if x.1 = y.1 then (s x.1 : ℚ)⁻¹ else 0

omit [Fintype κ] [∀ c, NeZero (s c)] in
theorem cycleAverage_symmetric : (cycleAverage s).IsSymm := by
  ext x y
  rcases x with ⟨c, i⟩
  rcases y with ⟨d, j⟩
  by_cases h : c = d
  · subst d
    rfl
  · simp [cycleAverage, h, Ne.symm h]

theorem cycleAverage_mul_left (M : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) ℚ)
    (c : κ) (i : ZMod (s c)) (y : Σ c, ZMod (s c)) :
    (cycleAverage s * M) ⟨c, i⟩ y = (s c : ℚ)⁻¹ * ∑ j, M ⟨c, j⟩ y := by
  simp only [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · simp only [cycleAverage, ite_true]
    rw [Finset.mul_sum]
  · intro d _ hdc
    simp [cycleAverage, Ne.symm hdc]
  · simp

theorem cycleAverage_mul_right (M : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) ℚ)
    (x : Σ c, ZMod (s c)) (d : κ) (j : ZMod (s d)) :
    (M * cycleAverage s) x ⟨d, j⟩ = (s d : ℚ)⁻¹ * ∑ k, M x ⟨d, k⟩ := by
  simp only [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single d]
  · simp only [cycleAverage, ite_true]
    rw [← Finset.sum_mul]
    ring
  · intro c _ hcd
    simp [cycleAverage, hcd]
  · simp

theorem cycleAverage_idempotent : cycleAverage s * cycleAverage s = cycleAverage s := by
  ext x y
  rcases x with ⟨c, i⟩
  rcases y with ⟨d, j⟩
  rw [cycleAverage_mul_left]
  by_cases h : c = d
  · subst d
    have hn : (s c : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne (s c)
    simp [cycleAverage, hn]
  · simp [cycleAverage, h]

theorem cycleAverage_mul_ones :
    cycleAverage s * (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) =
      (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) := by
  ext x y
  rcases x with ⟨c, i⟩
  rw [cycleAverage_mul_left]
  have hn : (s c : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne (s c)
  simp [hn]

theorem ones_mul_cycleAverage :
    (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) * cycleAverage s =
      (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) := by
  ext x y
  rcases y with ⟨d, j⟩
  rw [cycleAverage_mul_right]
  have hn : (s d : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne (s d)
  simp [hn]

variable (C : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) ℚ)
variable (hComm : ∀ c d (i : ZMod (s c)) (j : ZMod (s d)),
  C ⟨c, i⟩ ⟨d, j - 1⟩ + C ⟨c, i⟩ ⟨d, j + 1⟩ =
    C ⟨c, i - 1⟩ ⟨d, j⟩ + C ⟨c, i + 1⟩ ⟨d, j⟩)

include hComm

omit [Fintype κ] [DecidableEq κ] in
theorem cyclic_block_row_sum_constant (c d : κ) (i : ZMod (s c)) :
    (∑ j, C ⟨c, i⟩ ⟨d, j⟩) = ∑ j, C ⟨c, 0⟩ ⟨d, j⟩ := by
  apply cyclic_harmonic_constant (fun i => ∑ j, C ⟨c, i⟩ ⟨d, j⟩) _ i
  intro k
  have hSum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hComm c d k j)
  simp only [Finset.sum_add_distrib] at hSum
  have hPrev : (∑ j, C ⟨c, k⟩ ⟨d, j - 1⟩) = ∑ j, C ⟨c, k⟩ ⟨d, j⟩ := by
    simpa [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-1 : ZMod (s d)))
      (fun j => C ⟨c, k⟩ ⟨d, j⟩)
  have hNext : (∑ j, C ⟨c, k⟩ ⟨d, j + 1⟩) = ∑ j, C ⟨c, k⟩ ⟨d, j⟩ :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod (s d))) (fun j => C ⟨c, k⟩ ⟨d, j⟩)
  rw [hPrev, hNext] at hSum
  linarith

theorem cycleAverage_commutes (hSymm : C.IsSymm) : C * cycleAverage s = cycleAverage s * C := by
  have hValue (c : κ) (i k : ZMod (s c)) (y : Σ c, ZMod (s c)) :
      (C * cycleAverage s) ⟨c, k⟩ y = (C * cycleAverage s) ⟨c, i⟩ y := by
    rcases y with ⟨d, j⟩
    rw [cycleAverage_mul_right, cycleAverage_mul_right,
      cyclic_block_row_sum_constant s C hComm c d k, cyclic_block_row_sum_constant s C hComm c d i]
  have hECE : cycleAverage s * (C * cycleAverage s) = C * cycleAverage s := by
    ext x y
    rcases x with ⟨c, i⟩
    rw [cycleAverage_mul_left]
    simp only [hValue c i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
    have hn : (s c : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne (s c)
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hT := congrArg Matrix.transpose hECE
  simp only [Matrix.transpose_mul, (cycleAverage_symmetric s).eq, hSymm.eq] at hT
  rw [Matrix.mul_assoc] at hT
  exact hECE.symm.trans hT

theorem cycleAverage_product_trace :
    (C * cycleAverage s).trace = ∑ c, ∑ j, C ⟨c, 0⟩ ⟨c, j⟩ := by
  change (∑ x, (C * cycleAverage s) x x) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [cycleAverage_mul_right, cyclic_block_row_sum_constant s C hComm c c,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
  have hn : (s c : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne (s c)
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

end
end Erdos60Private

end


open Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


theorem binary_sum_mod_two_one_iff (x y : ℤ) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    ((x + y : ℤ) : ZMod 2) = 1 ↔ x ≠ y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

/-- The cyclic transition estimate and loop incidences give the completion loop bound. -/
theorem cyclic_matrix_loop_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : κ → ℕ) [∀ c, NeZero (s c)] (q : ℕ)
    (A : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) ℤ)
    (hSymm : A.IsSymm) (hBinary : ∀ x y, A x y = 0 ∨ A x y = 1)
    (hCard : Fintype.card (Σ c, ZMod (s c)) = q ^ 2 + q + 3)
    (hRow : ∀ x, (∑ y, A x y) = (q : ℤ) + 1)
    (hComm : ∀ c (i j : ZMod (s c)),
      A ⟨c, i⟩ ⟨c, j - 1⟩ + A ⟨c, i⟩ ⟨c, j + 1⟩ =
        A ⟨c, i - 1⟩ ⟨c, j⟩ + A ⟨c, i + 1⟩ ⟨c, j⟩)
    (hInternal : (∑ c, ∑ j, A ⟨c, 0⟩ ⟨c, j⟩) = (q : ℤ) + 1)
    (hOdd : ∀ c (i : ZMod (s c)),
      (∀ y, A ⟨c, i⟩ y = 0 ∨ A y y = 0) →
      (((A ⟨c, i⟩ ⟨c, i - 1⟩ + A ⟨c, i⟩ ⟨c, i + 1⟩) : ℤ) : ZMod 2) = 1) :
    (q : ℤ) - 3 ≤ A.trace := by
  let m : (Σ c, ZMod (s c)) → ℤ := fun x => ∑ y, A x y * A y y
  let t : (Σ c, ZMod (s c)) → ℤ := fun x =>
    if A x ⟨x.1, x.2 + 1⟩ ≠ A ⟨x.1, x.2 - 1⟩ x then 1 else 0
  have hNonneg (x y : Σ c, ZMod (s c)) : 0 ≤ A x y := by
    rcases hBinary x y with h | h <;> omega
  have hm (x) : 0 ≤ m x := Finset.sum_nonneg (fun y _ => mul_nonneg (hNonneg x y) (hNonneg y y))
  have ht (x) : 0 ≤ t x := by dsimp only [t]; split <;> omega
  have hOne (x : Σ c, ZMod (s c)) : 1 ≤ m x + t x := by
    by_cases hz : m x = 0
    · have hNoLoop (y) : A x y = 0 ∨ A y y = 0 := by
        have hLe : A x y * A y y ≤ m x :=
          Finset.single_le_sum (fun z _ => mul_nonneg (hNonneg x z) (hNonneg z z)) (Finset.mem_univ y)
        have hZero : A x y * A y y = 0 := by nlinarith only [hLe, hz, hNonneg x y, hNonneg y y]
        exact mul_eq_zero.mp hZero
      rcases x with ⟨c, i⟩
      have hParity := hOdd c i hNoLoop
      have hDifferent : A ⟨c, i⟩ ⟨c, i - 1⟩ ≠ A ⟨c, i⟩ ⟨c, i + 1⟩ :=
        (binary_sum_mod_two_one_iff _ _ (hBinary _ _) (hBinary _ _)).mp hParity
      have hTransition : t ⟨c, i⟩ = 1 := by
        dsimp only [t]
        have hNe : A ⟨c, i⟩ ⟨c, i + 1⟩ ≠ A ⟨c, i - 1⟩ ⟨c, i⟩ := by
          rw [hSymm.apply ⟨c, i⟩ ⟨c, i - 1⟩]
          exact Ne.symm hDifferent
        exact ite_eq_left hNe
      omega
    · have hPos : 1 ≤ m x := by have h := hm x; omega
      have h := ht x
      omega
  have hIncidences : (∑ x, m x) = ((q : ℤ) + 1) * A.trace := by
    dsimp only [m]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have hCol (y) : (∑ x, A x y) = (q : ℤ) + 1 := by
      calc
        (∑ x, A x y) = ∑ x, A y x := Finset.sum_congr rfl (fun x _ => hSymm.apply y x)
        _ = (q : ℤ) + 1 := hRow y
    simp only [hCol, ← Finset.mul_sum, Matrix.trace, Matrix.diag_apply]
  have hTransitions : (∑ x, t x) ≤ 4 * ((q : ℤ) + 1) := by
    have hEach (c : κ) := cyclic_binary_transition_bound
      (fun i j : ZMod (s c) => A ⟨c, i⟩ ⟨c, j⟩)
      (fun i j => hBinary _ _) (hComm c)
    have hSum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hEach c)
    simpa only [← Finset.mul_sum, hInternal, t, Fintype.sum_sigma] using hSum
  have hTotal := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hOne x)
  rw [Finset.sum_add_distrib, hIncidences] at hTotal
  have hOrder : (q : ℤ) ^ 2 + q + 3 ≤ ((q : ℤ) + 1) * A.trace + 4 * ((q : ℤ) + 1) := by
    have hN : (Fintype.card (Σ c, ZMod (s c)) : ℤ) = (q : ℤ) ^ 2 + q + 3 := by exact_mod_cast hCard
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, hN] at hTotal
    linarith
  by_contra h
  have hUpper : A.trace ≤ (q : ℤ) - 4 := by omega
  nlinarith [mul_le_mul_of_nonneg_left hUpper (show 0 ≤ (q : ℤ) + 1 by positivity)]

end Erdos60Private

end


open SimpleGraph Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


section
variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]
variable (s : κ → ℕ) [∀ c, NeZero (s c)] (H : SimpleGraph V)
variable (hDegree : ∀ v, H.degree v = 2) (e : (Σ c, ZMod (s c)) ≃ V)
variable (hNeighbors : ∀ c i, H.neighborFinset (e ⟨c, i⟩) = {e ⟨c, i - 1⟩, e ⟨c, i + 1⟩})

include hDegree hNeighbors

omit [Fintype κ] [DecidableEq κ] [∀ c, NeZero (s c)] in
theorem cyclic_neighbors_distinct (c : κ) (i : ZMod (s c)) :
    e ⟨c, i - 1⟩ ≠ e ⟨c, i + 1⟩ := by
  intro h
  have hCard := hDegree (e ⟨c, i⟩)
  rw [← H.card_neighborFinset_eq_degree, hNeighbors, h] at hCard
  simp at hCard

omit [DecidableEq κ] in
theorem cyclic_reindex_adj_mul {R : Type*} [Semiring R]
    (N : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) R)
    (c : κ) (i : ZMod (s c)) (y : Σ c, ZMod (s c)) :
    ((H.adjMatrix R).submatrix e e * N) ⟨c, i⟩ y =
      N ⟨c, i - 1⟩ y + N ⟨c, i + 1⟩ y := by
  let M := N.submatrix e.symm e.symm
  have hN : M.submatrix e e = N := by ext x y; simp [M]
  rw [← hN, Matrix.submatrix_mul_equiv]
  change (H.adjMatrix R * M) (e ⟨c, i⟩) (e y) = _
  rw [H.adjMatrix_mul_apply, hNeighbors, Finset.sum_pair (cyclic_neighbors_distinct s H hDegree e hNeighbors c i)]
  simp [M]

omit [DecidableEq κ] in
theorem cyclic_reindex_mul_adj {R : Type*} [Semiring R]
    (N : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) R)
    (x : Σ c, ZMod (s c)) (c : κ) (i : ZMod (s c)) :
    (N * (H.adjMatrix R).submatrix e e) x ⟨c, i⟩ =
      N x ⟨c, i - 1⟩ + N x ⟨c, i + 1⟩ := by
  let M := N.submatrix e.symm e.symm
  have hN : M.submatrix e e = N := by ext x y; simp [M]
  rw [← hN, Matrix.submatrix_mul_equiv]
  change (M * H.adjMatrix R) (e x) (e ⟨c, i⟩) = _
  rw [H.mul_adjMatrix_apply, hNeighbors, Finset.sum_pair (cyclic_neighbors_distinct s H hDegree e hNeighbors c i)]
  simp [M]

omit [DecidableEq κ] in
theorem cyclic_reindex_commutation {R : Type*} [Semiring R]
    (C : Matrix V V R) (hComm : C * H.adjMatrix R = H.adjMatrix R * C)
    (c d : κ) (i : ZMod (s c)) (j : ZMod (s d)) :
    C (e ⟨c, i⟩) (e ⟨d, j - 1⟩) + C (e ⟨c, i⟩) (e ⟨d, j + 1⟩) =
      C (e ⟨c, i - 1⟩) (e ⟨d, j⟩) + C (e ⟨c, i + 1⟩) (e ⟨d, j⟩) := by
  have h : C.submatrix e e * (H.adjMatrix R).submatrix e e =
      (H.adjMatrix R).submatrix e e * C.submatrix e e := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hComm]
  have hEntry := congrArg (fun M : Matrix (Σ c, ZMod (s c)) (Σ c, ZMod (s c)) R => M ⟨c, i⟩ ⟨d, j⟩) h
  rw [cyclic_reindex_mul_adj s H hDegree e hNeighbors, cyclic_reindex_adj_mul s H hDegree e hNeighbors] at hEntry
  exact hEntry

theorem cyclic_reindex_average_eigenvalue :
    (H.adjMatrix ℚ).submatrix e e * cycleAverage s = (2 : ℚ) • cycleAverage s := by
  ext x y
  rcases x with ⟨c, i⟩
  rw [cyclic_reindex_adj_mul s H hDegree e hNeighbors]
  simp only [cycleAverage, Matrix.smul_apply, smul_eq_mul]
  ring

end
end Erdos60Private

end


open SimpleGraph Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


/-- A regular binary completion with distinct-row Gram entries at most one has many loops. -/
theorem binary_completion_trace_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 2 < q) (hEven : Even q) (hNotSquare : ¬IsSquare ((q : ℚ) - 2))
    (C : Matrix V V ℤ) (hSymm : C.IsSymm)
    (hBinary : ∀ x y, C x y = 0 ∨ C x y = 1)
    (hCard : Fintype.card V = q ^ 2 + q + 3)
    (hRow : ∀ x, (∑ y, C x y) = (q : ℤ) + 1)
    (hGram : ∀ x y, x ≠ y → (C * C) x y ≤ 1) :
    (q : ℤ) - 3 ≤ C.trace := by
  let H := completionResidualGraph q C
  have hDegree : ∀ x, H.degree x = 2 :=
    completionResidualGraph_degree q C hSymm hBinary hCard hRow hGram
  have hAdj : H.adjMatrix ℤ = completionResidual q C :=
    completionResidualGraph_adjMatrix q C hSymm hBinary hRow hGram
  have hComm : C * H.adjMatrix ℤ = H.adjMatrix ℤ * C := by
    rw [hAdj]
    exact completionResidual_commutes q C hSymm hRow
  let f : Matrix V V ℤ →+* Matrix V V ℚ := (Int.castRingHom ℚ).mapMatrix
  let Cq := f C
  have hAdjq : f (H.adjMatrix ℤ) = H.adjMatrix ℚ := by
    ext x y
    simp [f, SimpleGraph.adjMatrix_apply]
  have hCommq : Cq * H.adjMatrix ℚ = H.adjMatrix ℚ * Cq := by
    simpa only [map_mul, hAdjq] using congrArg f hComm
  have hScalar : f ((q : ℤ) • (1 : Matrix V V ℤ)) = (q : ℚ) • (1 : Matrix V V ℚ) := by
    ext x y
    change (((q : ℤ) * (if x = y then (1 : ℤ) else 0) : ℤ) : ℚ) =
      (q : ℚ) * (if x = y then (1 : ℚ) else 0)
    by_cases h : x = y <;> simp [h]
  have hOnes : f (Matrix.of fun (_ : V) (_ : V) => (1 : ℤ)) =
      (Matrix.of fun (_ : V) (_ : V) => (1 : ℚ)) := by ext x y; simp [f]
  have hSquareInt : C * C = (q : ℤ) • (1 : Matrix V V ℤ) +
      (Matrix.of fun (_ : V) (_ : V) => (1 : ℤ)) - H.adjMatrix ℤ := by
    rw [hAdj]
    unfold completionResidual
    abel
  have hSquareQ : Cq * Cq = (q : ℚ) • (1 : Matrix V V ℚ) +
      (Matrix.of fun (_ : V) (_ : V) => (1 : ℚ)) - H.adjMatrix ℚ := by
    simpa only [map_mul, map_sub, map_add, hScalar, hOnes, hAdjq] using congrArg f hSquareInt
  obtain ⟨s, hs, e, hNeighbors⟩ := degree_two_cyclic_coordinates H hDegree
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let : DecidableEq H.ConnectedComponent := Classical.decEq _
  let : ∀ c, NeZero (s c) := fun c => ⟨by have h := hs c; omega⟩
  let A := C.submatrix e e
  let B := Cq.submatrix e e
  let Z := (H.adjMatrix ℚ).submatrix e e
  let E := cycleAverage s
  have hNewCard : Fintype.card (Σ c, ZMod (s c)) = q ^ 2 + q + 3 :=
    (Fintype.card_congr e).trans hCard
  have hABinary (x y) : A x y = 0 ∨ A x y = 1 := hBinary (e x) (e y)
  have hASymm : A.IsSymm := by ext x y; exact hSymm.apply (e x) (e y)
  have hARow (x) : (∑ y, A x y) = (q : ℤ) + 1 := by
    exact (Equiv.sum_comp e (fun y => C (e x) y)).trans (hRow (e x))
  have hBRow (x) : (∑ y, B x y) = (q : ℚ) + 1 := by
    change (∑ y, ((A x y : ℤ) : ℚ)) = (q : ℚ) + 1
    exact_mod_cast hARow x
  have hBSymm : B.IsSymm := by
    ext x y
    exact congrArg (fun z : ℤ => (z : ℚ)) (hSymm.apply (e x) (e y))
  have hCrossA := cyclic_reindex_commutation s H hDegree e hNeighbors C hComm
  have hCrossB := cyclic_reindex_commutation s H hDegree e hNeighbors Cq hCommq
  have hBSquare : B * B = (q : ℚ) • 1 +
      (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) - Z := by
    dsimp only [B, Z]
    rw [Matrix.submatrix_mul_equiv, hSquareQ]
    ext x y
    change (q : ℚ) * (if e x = e y then 1 else 0) + 1 - H.adjMatrix ℚ (e x) (e y) =
      (q : ℚ) * (if x = y then 1 else 0) + 1 - H.adjMatrix ℚ (e x) (e y)
    simp only [e.injective.eq_iff]
  have hBRows : B * (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) =
      ((q : ℚ) + 1) • (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) := by
    ext x y
    simpa only [Matrix.mul_apply, Matrix.of_apply, mul_one, Matrix.smul_apply, smul_eq_mul] using hBRow x
  have hBCols : (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) * B =
      ((q : ℚ) + 1) • (Matrix.of fun (_ : Σ c, ZMod (s c)) (_ : Σ c, ZMod (s c)) => (1 : ℚ)) := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.of_apply, one_mul, Matrix.smul_apply, smul_eq_mul, mul_one]
    calc
      (∑ x, B x y) = ∑ x, B y x := Finset.sum_congr rfl (fun x _ => hBSymm.apply y x)
      _ = (q : ℚ) + 1 := hBRow y
  have hTrace := completion_cycle_projection_trace q hq hNotSquare B Z E hNewCard hBSquare hBRows hBCols
    (cycleAverage_idempotent s) (cycleAverage_commutes s B hCrossB hBSymm)
    (ones_mul_cycleAverage s) (cycleAverage_mul_ones s)
    (cyclic_reindex_average_eigenvalue s H hDegree e hNeighbors)
  rw [cycleAverage_product_trace s B hCrossB] at hTrace
  have hInternal : (∑ c, ∑ j, A ⟨c, 0⟩ ⟨c, j⟩) = (q : ℤ) + 1 := by
    change (∑ c, ∑ j, ((A ⟨c, 0⟩ ⟨c, j⟩ : ℤ) : ℚ)) = (q : ℚ) + 1 at hTrace
    exact_mod_cast hTrace
  have hOdd (c) (i : ZMod (s c)) (hNoLoop : ∀ y, A ⟨c, i⟩ y = 0 ∨ A y y = 0) :
      (((A ⟨c, i⟩ ⟨c, i - 1⟩ + A ⟨c, i⟩ ⟨c, i + 1⟩) : ℤ) : ZMod 2) = 1 := by
    have hNoLoopC (y : V) : C (e ⟨c, i⟩) y = 0 ∨ C y y = 0 := by
      simpa only [A, Matrix.submatrix_apply, e.apply_symm_apply] using hNoLoop (e.symm y)
    have h := loop_free_row_residual_odd q C hSymm hBinary hRow hEven (e ⟨c, i⟩) hNoLoopC
    rw [← hAdj] at h
    have hEntry : (A * (H.adjMatrix ℤ).submatrix e e) ⟨c, i⟩ ⟨c, i⟩ =
        (C * H.adjMatrix ℤ) (e ⟨c, i⟩) (e ⟨c, i⟩) := by
      rw [Matrix.submatrix_mul_equiv]
      rfl
    rw [← hEntry, cyclic_reindex_mul_adj s H hDegree e hNeighbors] at h
    exact h
  have hBound := cyclic_matrix_loop_bound s q A hASymm hABinary hNewCard hARow
    (fun c i j => hCrossA c c i j) hInternal hOdd
  have hTraceA : A.trace = C.trace := Equiv.sum_comp e (fun x => C x x)
  simpa only [hTraceA] using hBound

end Erdos60Private

end


open Filter SimpleGraph Matrix
open scoped BigOperators Classical
noncomputable section
namespace Erdos60Private


theorem rational_not_square_sub_two (q : ℕ) (hMod : q % 4 = 0) :
    ¬IsSquare ((q : ℚ) - 2) := by
  intro h
  have hRat : IsSquare ((((q : ℤ) - 2) : ℤ) : ℚ) := by simpa using h
  have hInt := Rat.isSquare_intCast_iff.mp hRat
  obtain ⟨z, hz⟩ := (isSquare_iff_exists_sq ((q : ℤ) - 2)).mp hInt
  have hModInt : (q : ℤ) % 4 = 0 := by exact_mod_cast hMod
  have hBad : ((q : ℤ) - 2) % 4 = 2 := by omega
  rw [hz, Int.sq_emod_four] at hBad
  omega

theorem normalized_packing_excess_le_three (q a : ℕ) (hq : 2 < q)
    (hEven : Even q) (hMod : q % 4 = 0)
    (G : SimpleGraph (Fin (q ^ 2 + q + 2))) (hFree : (cycleGraph 4).Free G)
    (hEdges : G.edgeFinset.card = planeEdgeCount q + a)
    (P : Finset (Fin (q ^ 2 + q + 2))) (hCard : P.card = q) (hLow : P ⊆ lowVertices q G)
    (hOpen : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → codegree G v w = 0)
    (hIndependent : ∀ v ∈ P, ∀ w ∈ P, ¬G.Adj v w)
    (hUnit : ∀ v, signedDeficiency q G v = 0 ∨ signedDeficiency q G v = 1)
    (hOutsideTriangles : ∀ x ∈ lowVertices q G \ P, triangleTwice G x = 0)
    (hOutsideIndependent : ∀ x ∈ lowVertices q G \ P, ∀ y ∈ lowVertices q G \ P, ¬G.Adj x y) :
    a ≤ 3 := by
  have hOutsideZero (v) (hv : v ∈ lowVertices q G \ P) (w) (hAdj : G.Adj v w) : codegree G v w = 0 :=
    triangleTwice_zero_adj_codegree G v w (hOutsideTriangles v hv) hAdj
  have hOrder : Fintype.card (Option (Fin (q ^ 2 + q + 2))) = q ^ 2 + q + 3 := by simp
  have hBound := binary_completion_trace_lower_bound q hq hEven (rational_not_square_sub_two q hMod)
    (packingCompletion q G P) (packingCompletion_symmetric q G P) (packingCompletion_binary q G P)
    hOrder (packingCompletion_row_sum q G P hCard hLow hUnit)
    (packingCompletion_square_off_diagonal_le q G hFree P hOpen hIndependent hOutsideIndependent hOutsideZero)
  rw [packingCompletion_trace_of_excess q a G P hEdges hCard hLow hUnit] at hBound
  omega

/-- The exact square-root supersaturation assertion contradicts the completed extremizer. -/
theorem not_claimedBound : ¬ClaimedBound := by
  intro hBound
  obtain ⟨C, N, hC, hPrepared⟩ := claimedBound_uniform_normalized_packing hBound
  let k := N + 36 * C + 2
  let q := 2 ^ (2 * (k + 1))
  have hLarge : k < q := by
    have h : 2 * (k + 1) < 2 ^ (2 * (k + 1)) := Nat.lt_two_pow_self
    dsimp only [q]
    omega
  have hN : N ≤ q := by dsimp only [k] at hLarge; omega
  have hq : 2 < q := by dsimp only [k] at hLarge; omega
  have hqForm : q = 4 * 2 ^ (2 * k) := by
    dsimp only [q]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    norm_num
    ring
  have hEven : Even q := by
    refine ⟨2 * 2 ^ (2 * k), ?_⟩
    rw [hqForm]
    ring
  have hMod : q % 4 = 0 := by rw [hqForm]; omega
  obtain ⟨G, hFree, hEdges, hMin⟩ := exists_minimizing_extremizer (q ^ 2 + q + 2) triangleWeightedObjective
  have hEdgesFinset : G.edgeFinset.card = extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) := by
    simpa only [edgeSet_ncard] using hEdges
  have hMinimal (J : SimpleGraph (Fin (q ^ 2 + q + 2))) (hJ : (cycleGraph 4).Free J)
      (hJE : J.edgeFinset.card = G.edgeFinset.card) : triangleWeightedObjective G ≤ triangleWeightedObjective J := by
    apply hMin J hJ
    simpa only [edgeSet_ncard] using hJE.trans hEdgesFinset
  obtain ⟨hExcess, P, hCard, hLow, hOpen, hIndependent, hUnit, _hPUnit, hTriangle, hOutside⟩ :=
    hPrepared k hN G hFree hEdgesFinset hMinimal
  let a := abovePlaneExcess q
  change q ≤ 4 * C * a ^ 2 at hExcess
  have hPositive : 0 < a := by
    by_contra h
    have ha : a = 0 := by omega
    rw [ha] at hExcess
    norm_num at hExcess
    omega
  have hPlaneEdges : G.edgeFinset.card = planeEdgeCount q + a := by
    rw [hEdgesFinset]
    change extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) = planeEdgeCount q +
      (extremalNumber (q ^ 2 + q + 2) (cycleGraph 4) - planeEdgeCount q)
    dsimp only [a, abovePlaneExcess] at hPositive
    omega
  have ha := normalized_packing_excess_le_three q a hq hEven hMod G hFree hPlaneEdges
    P hCard hLow hOpen hIndependent hUnit hTriangle hOutside
  have hSmall : q ≤ 36 * C := by
    have hASq : a ^ 2 ≤ 9 := by nlinarith
    have hScale := Nat.mul_le_mul_left (4 * C) hASq
    nlinarith only [hExcess, hScale]
  dsimp only [k] at hLarge
  omega

end Erdos60Private

end

end Bounty
