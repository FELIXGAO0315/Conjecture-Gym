/-
PolyForge — graph domain Lean library (v1.1, stage 1).

The graph analogue of HexLemmas.lean: a small, self-proved lemma base on top of
Mathlib's graph theory, providing the inventory facts that are NOT already named
Mathlib lemmas, plus the ℕ∞→ℕ (`toNat`) finiteness/conversion forms the generated
conjectures are stated in.  No `sorry`, no axioms.

Invariant ↔ Lean (see domains/graph/inventory.py):
  n→Fintype.card V, m→edgeFinset.card, max_deg→maxDegree, min_deg→minDegree,
  chi→chromaticNumber.toNat, omega→cliqueNum, alpha→indepNum,
  tau→vertexCoverNum.toNat, diam→diam, radius→radius.toNat, girth→girth.
-/
import Mathlib

open Finset SimpleGraph

-- these lemmas share one `variable` block; some don't use every instance
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace PolyForge.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### max degree ≤ edges (inventory 5, from v1.0) -/

theorem maxDegree_le_card_edgeFinset :
    G.maxDegree ≤ G.edgeFinset.card :=
  G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)

/-! ### finiteness of the chromatic number -/

theorem chromaticNumber_ne_top : G.chromaticNumber ≠ ⊤ := by
  intro htop
  have h := G.chromaticNumber_le_card
  rw [htop] at h
  exact (ENat.natCast_ne_top (Fintype.card V)) (top_le_iff.mp h)

/-! ### positivity (n ≥ 1) : ω ≥ 1, α ≥ 1, χ ≥ 1 (inventory 8) -/

theorem one_le_cliqueNum [Nonempty V] : 1 ≤ G.cliqueNum := by
  have h := IsClique.card_le_cliqueNum (G := G) (t := {Classical.arbitrary V}) (by simp)
  simpa using h

theorem one_le_indepNum [Nonempty V] : 1 ≤ G.indepNum := by
  have h := IsIndepSet.card_le_indepNum (G := G) (t := {Classical.arbitrary V}) (by simp)
  simpa using h

/-- ω ≤ χ as a ℕ statement (inventory 1, toNat form). -/
theorem cliqueNum_le_chromaticNumber_toNat :
    G.cliqueNum ≤ G.chromaticNumber.toNat := by
  have h := ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (chromaticNumber_ne_top G)
  simpa using h

/-- χ ≤ n as a ℕ statement (inventory 2, toNat form). -/
theorem chromaticNumber_toNat_le_card :
    G.chromaticNumber.toNat ≤ Fintype.card V := by
  have h := ENat.toNat_le_toNat G.chromaticNumber_le_card (ENat.natCast_ne_top (Fintype.card V))
  simpa using h

theorem one_le_chromaticNumber_toNat [Nonempty V] : 1 ≤ G.chromaticNumber.toNat :=
  (one_le_cliqueNum G).trans (cliqueNum_le_chromaticNumber_toNat G)

/-! ### Gallai identity α + τ = n (inventory 7) -/

theorem indepNum_add_vertexCoverNum_toNat :
    G.indepNum + G.vertexCoverNum.toNat = Fintype.card V := by
  classical
  -- a maximum independent set s (Finset) with #s = indepNum
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hs_indep : G.IsIndepSet ↑s := hs.isIndepSet
  have hs_card : s.card = G.indepNum := hs.card_eq
  -- a minimum vertex cover c (Set) with c.encard = vertexCoverNum
  obtain ⟨c, hc_enc, hc_cover⟩ := G.vertexCoverNum_exists
  -- τ = c.ncard
  have hc_ncard : c.ncard = G.vertexCoverNum.toNat := by
    rw [Set.ncard, hc_enc]
  -- cᶜ independent ⟹ #cᶜ ≤ indepNum
  have ind_c : G.IsIndepSet cᶜ := isIndepSet_compl_iff_isVertexCover.mpr hc_cover
  have hcompl_le : cᶜ.ncard ≤ G.indepNum := by
    have hle := IsIndepSet.card_le_indepNum (G := G) (t := cᶜ.toFinset)
      (by simpa [Set.coe_toFinset] using ind_c)
    simpa [Set.ncard_eq_toFinset_card'] using hle
  -- c and cᶜ partition the vertex set
  have hsum : c.ncard + cᶜ.ncard = Fintype.card V := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  -- (↑s)ᶜ is a vertex cover ⟹ τ ≤ n − indepNum
  have cov_s : IsVertexCover G ((↑s : Set V)ᶜ) := isVertexCover_compl.mpr hs_indep
  have hsc_ncard : ((↑s : Set V)ᶜ).ncard = Fintype.card V - G.indepNum := by
    rw [Set.ncard_compl, Set.ncard_coe_finset, hs_card, Nat.card_eq_fintype_card]
  have h_upper : G.vertexCoverNum.toNat ≤ Fintype.card V - G.indepNum := by
    have h1 := cov_s.vertexCoverNum_le
    have hfin : ((↑s : Set V)ᶜ).encard ≠ ⊤ := (Set.toFinite _).encard_lt_top.ne
    have h2 := ENat.toNat_le_toNat h1 hfin
    rw [← Set.ncard] at h2
    rwa [hsc_ncard] at h2
  -- indepNum ≤ n
  have hind_le : G.indepNum ≤ Fintype.card V := by
    rw [← hs_card]; exact (s.card_le_univ).trans_eq (by simp)
  omega

/-! ### vertex cover : τ ≤ n − 1 (inventory 6), via Gallai + α ≥ 1 -/

theorem vertexCoverNum_toNat_le_card_sub_one [Nonempty V] :
    G.vertexCoverNum.toNat ≤ Fintype.card V - 1 := by
  have hg := indepNum_add_vertexCoverNum_toNat G
  have ha := one_le_indepNum G
  omega

/-! ### radius ≤ diam ≤ 2·radius (connected; inventory 9) -/

theorem radius_toNat_le_diam (h : G.Connected) :
    G.radius.toNat ≤ G.diam := by
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have hle : G.radius ≤ G.ediam := SimpleGraph.radius_le_ediam
  simpa [SimpleGraph.diam] using ENat.toNat_le_toNat hle hne

theorem diam_le_two_mul_radius_toNat (h : G.Connected) :
    G.diam ≤ 2 * G.radius.toNat := by
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have hrne : G.radius ≠ ⊤ :=
    fun hr => hne (SimpleGraph.ediam_eq_top_iff_radius_eq_top.mpr hr)
  have hcoe : (G.radius.toNat : ℕ∞) = G.radius := ENat.natCast_toNat hrne
  have hb : G.ediam ≤ ((2 * G.radius.toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, hcoe]; exact G.ediam_le_two_mul_radius
  have ht := ENat.toNat_le_toNat hb (ENat.natCast_ne_top _)
  simpa [SimpleGraph.diam] using ht

/-! ### k-edge-connected ⟹ min_deg ≥ k (inventory 17) -/

theorem isEdgeConnected_le_minDegree [Nontrivial V] {k : ℕ}
    (h : G.IsEdgeConnected k) : k ≤ G.minDegree :=
  G.le_minDegree_of_forall_le_degree k (fun _ => h.le_degree)

/-! ### ℤ wrapper lemmas (v1.1 §I.2)

One per inventory entry, stating the relation in ℤ over the invariant
expressions (n→card, m→edgeFinset.card, max_deg/min_deg→max/minDegree,
chi→chromaticNumber.toNat, omega→cliqueNum, alpha→indepNum,
tau→vertexCoverNum.toNat, diam→diam, radius→radius.toNat, girth→girth).  The
graph formalizer `have`-introduces exactly these and closes with linarith/omega.
Property hypotheses are stated in the v1.1 §I.3 forms; positivity/nontriviality
are supplied as card bounds (`1 ≤ card` / `2 ≤ card`) and the Nonempty/Nontrivial
instances are derived inside. -/

-- 1
theorem omega_le_chi_int : (G.cliqueNum : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  exact_mod_cast cliqueNum_le_chromaticNumber_toNat G
-- 2
theorem chi_le_n_int : (G.chromaticNumber.toNat : ℤ) ≤ (Fintype.card V : ℤ) := by
  exact_mod_cast chromaticNumber_toNat_le_card G
-- 3
theorem min_le_max_int : (G.minDegree : ℤ) ≤ (G.maxDegree : ℤ) := by
  exact_mod_cast G.minDegree_le_maxDegree
-- 4
theorem max_lt_card_int (hn : 1 ≤ Fintype.card V) :
    (G.maxDegree : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have h := G.maxDegree_lt_card_verts
  omega
-- 5
theorem max_le_edges_int : (G.maxDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  exact_mod_cast maxDegree_le_card_edgeFinset G
-- 6
theorem tau_le_card_sub_one_int (hn : 1 ≤ Fintype.card V) :
    (G.vertexCoverNum.toNat : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have h := vertexCoverNum_toNat_le_card_sub_one G
  omega
-- 7
theorem gallai_int :
    (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = (Fintype.card V : ℤ) := by
  exact_mod_cast indepNum_add_vertexCoverNum_toNat G
-- 8a
theorem chi_ge_one_int (hn : 1 ≤ Fintype.card V) : (1 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact_mod_cast one_le_chromaticNumber_toNat G
-- 8b
theorem omega_ge_one_int (hn : 1 ≤ Fintype.card V) : (1 : ℤ) ≤ (G.cliqueNum : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact_mod_cast one_le_cliqueNum G
-- 8c
theorem alpha_ge_one_int (hn : 1 ≤ Fintype.card V) : (1 : ℤ) ≤ (G.indepNum : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact_mod_cast one_le_indepNum G
-- 9a
theorem radius_le_diam_int (h : G.Connected) :
    (G.radius.toNat : ℤ) ≤ (G.diam : ℤ) := by
  exact_mod_cast radius_toNat_le_diam G h
-- 9b
theorem diam_le_two_radius_int (h : G.Connected) :
    (G.diam : ℤ) ≤ 2 * (G.radius.toNat : ℤ) := by
  have := diam_le_two_mul_radius_toNat G h; omega
-- 10
theorem tree_edges_int (h : G.IsTree) :
    (G.edgeFinset.card : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have := h.card_edgeFinset; omega
-- 11
theorem tree_min_deg_int (h : G.IsTree) (hn : 2 ≤ Fintype.card V) :
    (G.minDegree : ℤ) = 1 := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := h.minDegree_eq_one_of_nontrivial; omega
-- 12
theorem acyclic_chi_int (h : G.IsAcyclic) : (G.chromaticNumber.toNat : ℤ) ≤ 2 := by
  have h2 := ENat.toNat_le_toNat h.chromaticNumber_le_two (by simp)
  simp only [ENat.toNat_ofNat] at h2
  exact_mod_cast h2
-- 13
theorem girth_le_diam_int (h : G.Connected) (_hc : ¬ G.IsAcyclic) :
    (G.girth : ℤ) ≤ 2 * (G.diam : ℤ) + 1 := by
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have := G.girth_le_two_mul_diam_add_one hne; omega
-- 14
theorem girth_ge_three_int (hc : ¬ G.IsAcyclic) : (3 : ℤ) ≤ (G.girth : ℤ) := by
  have := G.three_le_girth hc; omega
-- 15
theorem connected_min_deg_int (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (1 : ℤ) ≤ (G.minDegree : ℤ) := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := h.preconnected.minDegree_pos_of_nontrivial; omega
-- 16a
theorem regular_max_int {d : ℕ} (h : G.IsRegularOfDegree d) (hn : 1 ≤ Fintype.card V) :
    (G.maxDegree : ℤ) = (d : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have := h.maxDegree_eq; omega
-- 16b
theorem regular_min_int {d : ℕ} (h : G.IsRegularOfDegree d) (hn : 1 ≤ Fintype.card V) :
    (G.minDegree : ℤ) = (d : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have := h.minDegree_eq; omega
-- 17
theorem edge_conn_min_deg_int {k : ℕ} (h : G.IsEdgeConnected k) (hn : 2 ≤ Fintype.card V) :
    (k : ℤ) ≤ (G.minDegree : ℤ) := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := isEdgeConnected_le_minDegree G h; omega
-- bipartite ⟺ chi ≤ 2 (property premise → numeric chi fact, §II.3)
theorem bipartite_chi_int (h : G.IsBipartite) : (G.chromaticNumber.toNat : ℤ) ≤ 2 := by
  have h2 := ENat.toNat_le_toNat (chromaticNumber_le_two_iff_isBipartite.mpr h) (by simp)
  simp only [ENat.toNat_ofNat] at h2
  exact_mod_cast h2
theorem not_bipartite_chi_int (h : ¬ G.IsBipartite) : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  have hne := chromaticNumber_ne_top G
  have h2 : ¬ (G.chromaticNumber ≤ 2) := fun hc => h (chromaticNumber_le_two_iff_isBipartite.mp hc)
  have h3 : (2 : ℕ∞) < G.chromaticNumber := not_le.mp h2
  rw [← ENat.natCast_toNat hne] at h3
  have h4 : 2 < G.chromaticNumber.toNat := by exact_mod_cast h3
  omega

/-! ### v1.1.1 elementary facts -/

-- connected + nontrivial ⟹ diam ≥ 1
theorem one_le_diam_of_connected (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    1 ≤ G.diam := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have h1 : 1 ≤ G.ediam := Order.one_le_iff_ne_zero.mpr G.ediam_ne_zero
  have := ENat.toNat_le_toNat h1 hne
  simpa [SimpleGraph.diam] using this

-- connected + nontrivial ⟹ radius ≥ 1
theorem one_le_radius_of_connected (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    1 ≤ G.radius.toNat := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have hrne : G.radius ≠ ⊤ :=
    fun hr => hne (SimpleGraph.ediam_eq_top_iff_radius_eq_top.mpr hr)
  have hz : G.radius ≠ 0 := by
    intro heq
    rw [SimpleGraph.radius_eq_zero_iff] at heq
    exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial V›) heq.2
  have h1 : 1 ≤ G.radius := Order.one_le_iff_ne_zero.mpr hz
  have := ENat.toNat_le_toNat h1 hrne
  simpa using this

-- connected ⟹ m ≥ n − 1
theorem card_edgeFinset_ge_card_sub_one (h : G.Connected) :
    Fintype.card V ≤ G.edgeFinset.card + 1 := by
  have h1 := h.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h1
  have hE : Nat.card (↑G.edgeSet) = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]; rfl
  rw [hE] at h1; exact h1

/-! ### v1.1.1 ℤ wrappers -/

theorem diam_ge_one_int (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (1 : ℤ) ≤ (G.diam : ℤ) := by
  have := one_le_diam_of_connected G h hn; omega

theorem radius_ge_one_int (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (1 : ℤ) ≤ (G.radius.toNat : ℤ) := by
  have := one_le_radius_of_connected G h hn; omega

theorem connected_edges_int (h : G.Connected) :
    (Fintype.card V : ℤ) - 1 ≤ (G.edgeFinset.card : ℤ) := by
  have := card_edgeFinset_ge_card_sub_one G h; omega

/-! ### v1.1.2 §I: nonempty-unconditional ℤ wrappers (graphs assumed [Nonempty V]) -/

theorem card_ge_one_int [Nonempty V] : (1 : ℤ) ≤ (Fintype.card V : ℤ) := by
  have h0 : 1 ≤ Fintype.card V := Fintype.card_pos
  exact_mod_cast h0

theorem max_lt_card_int' [Nonempty V] :
    (G.maxDegree : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  have := G.maxDegree_lt_card_verts; omega

theorem tau_le_card_sub_one_int' [Nonempty V] :
    (G.vertexCoverNum.toNat : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  have := vertexCoverNum_toNat_le_card_sub_one G
  have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
  omega

theorem chi_ge_one_int' [Nonempty V] : (1 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  exact_mod_cast one_le_chromaticNumber_toNat G

theorem omega_ge_one_int' [Nonempty V] : (1 : ℤ) ≤ (G.cliqueNum : ℤ) := by
  exact_mod_cast one_le_cliqueNum G

theorem alpha_ge_one_int' [Nonempty V] : (1 : ℤ) ≤ (G.indepNum : ℤ) := by
  exact_mod_cast one_le_indepNum G

theorem regular_max_int' [Nonempty V] {d : ℕ} (h : G.IsRegularOfDegree d) :
    (G.maxDegree : ℤ) = (d : ℤ) := by
  have := h.maxDegree_eq; omega

theorem regular_min_int' [Nonempty V] {d : ℕ} (h : G.IsRegularOfDegree d) :
    (G.minDegree : ℤ) = (d : ℤ) := by
  have := h.minDegree_eq; omega

/-! ### v1.1.2 §II: elementary facts -/

-- alpha ≤ n  (independence number ≤ vertices)
theorem indepNum_le_card : G.indepNum ≤ Fintype.card V := by
  have h : Gᶜ.cliqueNum = G.indepNum := cliqueNum_compl
  have h2 := Gᶜ.cliqueNum_le_natCard
  rw [Nat.card_eq_fintype_card, h] at h2; exact h2

theorem alpha_le_card_int : (G.indepNum : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := indepNum_le_card G; omega

-- omega ≤ n  (clique number ≤ vertices)
theorem omega_le_card_int : (G.cliqueNum : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := G.cliqueNum_le_natCard; rw [Nat.card_eq_fintype_card] at this; omega

-- tau ≤ m  (vertex-cover number ≤ edges)
theorem vertexCoverNum_toNat_le_edges : G.vertexCoverNum.toNat ≤ G.edgeFinset.card := by
  have h := G.vertexCoverNum_le_encard_edgeSet
  have henc : G.edgeSet.encard = (G.edgeFinset.card : ℕ∞) := by
    rw [Set.encard_eq_coe_toFinset_card]; rfl
  rw [henc] at h
  exact (ENat.toNat_le_toNat h (ENat.natCast_ne_top _)).trans_eq (ENat.toNat_coe _)

theorem tau_le_edges_int : (G.vertexCoverNum.toNat : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have := vertexCoverNum_toNat_le_edges G; omega

-- has_cycle ⟹ nontrivial  (a graph with a cycle has ≥ 2 vertices)
theorem hasCycle_two_le_card (h : ¬ G.IsAcyclic) : 2 ≤ Fintype.card V := by
  by_contra hc
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hbot : G = ⊥ := by
    ext a b; simp only [bot_adj, iff_false]
    exact fun hab => hab.ne (Subsingleton.elim a b)
  exact h (hbot ▸ isAcyclic_bot)

theorem hasCycle_two_le_card_int (h : ¬ G.IsAcyclic) : (2 : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := hasCycle_two_le_card G h; omega

-- is_connected ∧ has_cycle ⟹ m ≥ n
theorem conn_cycle_card_le_edges (hconn : G.Connected) (hcyc : ¬ G.IsAcyclic) :
    Fintype.card V ≤ G.edgeFinset.card := by
  have hle := card_edgeFinset_ge_card_sub_one G hconn
  by_contra hlt
  rw [not_le] at hlt
  have heq : G.edgeFinset.card + 1 = Fintype.card V := by omega
  have htree : G.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
    exact heq
  exact hcyc htree.isAcyclic

theorem conn_cycle_edges_ge_card_int (hconn : G.Connected) (hcyc : ¬ G.IsAcyclic) :
    (Fintype.card V : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have := conn_cycle_card_le_edges G hconn hcyc; omega

/-! ### property-implication discharge (§II.2, used by the formalizer) -/

theorem isTree_connected (h : G.IsTree) : G.Connected := h.connected
theorem isTree_acyclic (h : G.IsTree) : G.IsAcyclic := h.isAcyclic
theorem isAcyclic_bipartite (h : G.IsAcyclic) : G.IsBipartite :=
  chromaticNumber_le_two_iff_isBipartite.mp h.chromaticNumber_le_two

end PolyForge.Graph
