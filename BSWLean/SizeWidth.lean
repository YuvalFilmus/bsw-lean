import BSWLean.Treelike
import BSWLean.TinyConversions
import Mathlib.Data.Finset.Basic

def TreeLikeResolution.width {vars} {φ : CNFFormula vars} :
    ∀ {c : Clause vars}, TreeLikeResolution φ c → Nat
  | C, .axiom_clause _ => C.card
  | C, .resolve _ _ _ _ _ π₁ π₂ _ => max C.card (max (width π₁) (width π₂))

lemma card_combination {vars} {sub_vars} {ρ : Assignment sub_vars}
    (c : Clause (vars \ sub_vars)) (C : Clause (vars \ sub_vars)) {h₁ h₂}
    : Finset.card ((C.combine ρ.toClause h₁).convert_trivial vars h₂)
    ≤ Finset.card C + (Finset.card sub_vars) := by
  unfold Clause.combine
  simp
  have idea₁ : Finset.card (C.convert (Finset.disjUnion (vars \ sub_vars) sub_vars h₁)
    (Clause.combine._proof_1 C h₁ : ∀ l ∈ C, l.variable ∈ Finset.disjUnion (vars \ sub_vars) sub_vars h₁))
    ≤ (Finset.card C) := by
    simp
  have idea₂: Finset.card (ρ.toClause.convert (Finset.disjUnion (vars \ sub_vars) sub_vars h₁)
    (Clause.combine._proof_2 ρ.toClause h₁ : ∀ l ∈ ρ.toClause, l.variable ∈ Finset.disjUnion (vars \ sub_vars) sub_vars h₁))
    ≤ Finset.card sub_vars := by
    simp
    exact to_clause_card_less_than_sub_vars_card ρ
  grind only [usr Finset.card_union_add_card_inter]

lemma resolve_subsets (x : Variable) (vars) (c₁ c₂ c₃ c₄ : Clause (vars))
    (h_x : x ∈ vars) (h₁ : c₁ ⊆ c₃) (h₂ : c₂ ⊆ c₄) : (c₁.resolve c₂ x h_x) ⊆ (c₃.resolve c₄ x h_x)
    := by
    unfold Clause.resolve
    grind

lemma resolve_subsets_trick (x : Variable) (vars) (c₁ c₂ c₃ : Clause (vars))
    (h_x : x ∈ vars) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h_x}) (h₂: c₃ ⊆ c₁ ∪ {x.toNegLiteral h_x}) : Finset.card (c₂.resolve c₃ x h_x) ≤ Finset.card c₁
    := by
    unfold Clause.resolve
    have idea : (Finset.erase c₂ (x.toLiteral h_x) ∪ Finset.erase c₃ (x.toNegLiteral h_x)) ⊆ c₁
      := by
      simp_all only [Finset.union_singleton]
      grind
    exact Finset.card_le_card idea

lemma clause_combine_superset (vars₁ vars₂) {x : Variable} (c₁ c₂: Clause (vars₁)) (c₃ : Clause (vars₂))
    (h₀ : x ∈ vars₁) (h₁ : c₂ ⊆ c₁ ∪ {x.toLiteral h₀}) (h_disj: Disjoint vars₁ vars₂) (h₂ : x ∈ (vars₁.disjUnion vars₂ h_disj)):
    (Clause.combine c₂ c₃ h_disj) ⊆ ((Clause.combine c₁ c₃ h_disj) ∪ {x.toLiteral h₂})
    := by
    simp
    unfold Clause.combine
    simp
    refine Finset.union_subset ?_ ?_
    trans insert (x.toLiteral h₂) (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop))
    refine
      Clause.convert_maintains_subset_insert c₂ c₁ (Finset.disjUnion vars₁ vars₂ h_disj)
        (x.toLiteral h₂) h₀ ?_
    simp_all only [Finset.union_singleton]
    exact h₁
    simp
    trans (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∪ c₃.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop))
    simp
    simp

@[aesop safe]
lemma loose_convert {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} (h_subset : c₁ ⊆ c₂) :
    (c₁.convert vars₂ h₁) ⊆ (c₂.convert vars₂ h₂) := by
  exact Clause.convert_keeps_subset vars₂ h_subset

@[simp]
lemma loose_convert_eq {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} (h_subset : c₁ = c₂) :
    (c₁.convert vars₂ h₁) = (c₂.convert vars₂ h₂) := by
  aesop

@[aesop safe]
lemma loose_convert_trivial {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} (h_subset : c₁ ⊆ c₂) :
    (c₁.convert_trivial vars₂ h₁) ⊆ (c₂.convert_trivial vars₂ h₂) := by
  unfold Clause.convert_trivial
  aesop

@[simp]
lemma carry_through_convert {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁} :
    ((c₁ ∪ c₂).convert vars₂ h₁) =
    (c₁.convert vars₂ (by aesop)) ∪ (c₂.convert vars₂ (by aesop)) := by
  unfold Clause.convert
  aesop

@[simp]
lemma carry_through_convert₂ {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂ h₃} :
    ((c₁ ∪ c₂).convert vars₂ h₁) =
    (c₁.convert vars₂ h₂) ∪ (c₂.convert vars₂ h₃) := by
  unfold Clause.convert
  aesop

@[simp]
lemma carry_through_convert_expl (vars₁ vars₂) (c₁ c₂ : Clause vars₁) (h₁ h₂ h₃) :
    ((c₁ ∪ c₂).convert vars₂ h₁) =
    (c₁.convert vars₂ h₂) ∪ (c₂.convert vars₂ h₃) := by
  unfold Clause.convert
  aesop

@[simp]
lemma carry_through_convert_expl_lit (vars₁ vars₂) (c₁ : Clause vars₁)
    (l : Literal vars₁) (h₁ h₂ h₃) :
    ((c₁ ∪ {l}).convert vars₂ h₁) =
    (c₁.convert vars₂ h₂) ∪ {(l.convert vars₂ h₃)} := by
  unfold Clause.convert
  aesop


@[simp]
lemma carry_through_convert_trivial {vars₁ vars₂} (c₁ c₂ : Clause vars₁) {h₁ h₂} :
    ((c₁ ∪ c₂).convert_trivial vars₂ h₁) =
    (c₁.convert_trivial vars₂ h₂) ∪ (c₂.convert_trivial vars₂ h₂) := by
  unfold Clause.convert_trivial
  aesop

lemma cup_subset_cup {α} [DecidableEq α] (a b c d : Finset α) (h : a ⊆ c) (h' : b ⊆ d) :
    (a ∪ b) ⊆ (c ∪ d) := by
  grind

lemma remove_middle_subset {α} [DecidableEq α] (a b c d : Finset α) (h : a ⊆ b ∪ d) :
    a ⊆ b ∪ c ∪ d := by grind

lemma subset_of_vars_clause (vars₁ vars₂) (c : Clause vars₁) (h : vars₁ ⊆ vars₂) :
    ∀ l ∈ c, l.variable ∈ vars₂ := by aesop



lemma inter_idea_new_version (vars sub_vars) (lit : Literal (vars \ sub_vars))
    (ρ : Assignment sub_vars) (c_1 c_2 : Clause (vars \ sub_vars))
    (inter_proof : Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint
      : Disjoint (vars \ sub_vars) sub_vars) = vars)
    (var_incl : lit.variable ∈ vars)
    (left : c_2 ⊆ c_1 ∪ {lit}):
    ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ⊆
    ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ∪ {lit.convert vars var_incl} := by
  have h_subset : sub_vars ⊆ vars := by aesop
  have : Clause.convert {lit} vars
      (by intro l h_l; have q := Literal.variable_mem_vars l; aesop) =
      {lit.convert vars var_incl} := by
    unfold Clause.convert
    simp only [Finset.mem_singleton]
    aesop
  rw [←this]
  have fact : (Finset.disjUnion (vars \ sub_vars) sub_vars
      (Finset.sdiff_disjoint : Disjoint (vars \ sub_vars) sub_vars)) = vars := by
    aesop
  unfold Clause.combine
  unfold Clause.convert_trivial
  simp only [carry_through_convert, Finset.union_assoc]
  apply Finset.union_subset
  swap
  · grind
  rw [←Finset.union_assoc]
  apply remove_middle_subset
  rw [this]
  have fact₁ : (vars \ sub_vars) ⊆ vars := by aesop
  have fact₂ : ∀ l ∈ c_2, l.variable ∈ vars := by
    exact fun l a ↦
      subset_of_vars_clause (vars \ sub_vars) vars (c_1 ∪ {lit}) fact₁ l (left a)
  have fact₃ : ∀ l ∈ c_1, l.variable ∈ vars := by
    exact fun l a ↦ subset_of_vars_clause (vars \ sub_vars) vars c_1 fact₁ l a
  have fact₄ : ∀ l ∈ (c_1 ∪ {lit}), l.variable ∈ vars := by
    exact fun l a ↦
      subset_of_vars_clause (vars \ sub_vars) vars (c_1 ∪ {lit}) fact₁ l a
  have fact₅ : ∀ l ∈ (c_1 ∪ {lit}), l.variable ∈ (vars \ sub_vars) := by
    exact fun l a ↦
      subset_of_vars_clause (vars \ sub_vars) (vars \ sub_vars) (c_1 ∪ {lit})
        (fun ⦃a⦄ a_1 ↦ a_1) l a
  have fact₅ : (lit).variable ∈ vars := by
    aesop
  trans c_2.convert vars fact₂
  · aesop
  trans ((c_1 ∪ {lit}).convert vars fact₄)
  · aesop
  trans (c_1.convert  vars fact₃) ∪ {lit.convert vars var_incl}
  trans (c_1.convert  vars fact₃) ∪ {((lit).convert vars fact₅)}
  have final_idea : ((lit).convert vars fact₅) = lit.convert vars var_incl := by
    aesop
  refine Finset.subset_of_eq ?_
  exact carry_through_convert_expl_lit (vars \ sub_vars) vars c_1 (lit) fact₄ fact₃ (by aesop)
  · aesop
  aesop


lemma resolve_ineq (vars sub_vars) (φ : CNFFormula vars) (var : Variable)
    (ρ : Assignment sub_vars) (c c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4})
    (right : c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4}):
    Finset.card ((TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
    (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset) ≤
    max (Finset.card c_1) (max p_1.width p_2.width) + Finset.card sub_vars := by
  unfold TreeLikeResolution.unsubstitute_rhs
  simp
  have inter_proof : Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint : Disjoint (vars \ sub_vars) sub_vars) = vars := by
    aesop
  have var_incl : var ∈ vars := by
    grind
  have idea₁ : (p_1.unsubstitute_rhs ρ h_subset) ⊆
    (Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (inter_proof)
    := by
    exact TreeLikeResolution.unsubstitute_rhs_variables ρ p_1 h_subset
  have idea₂ : (p_2.unsubstitute_rhs ρ h_subset) ⊆
    (Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (inter_proof)
    := by
    exact TreeLikeResolution.unsubstitute_rhs_variables ρ p_2 h_subset

  trans Finset.card (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof).resolve
    ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) var (Finset.sdiff_subset h_4 : var ∈ vars))

  have inter_idea :
    ((p_1.unsubstitute_rhs ρ h_subset).resolve (p_2.unsubstitute_rhs ρ h_subset) var (Finset.sdiff_subset h_4 : var ∈ vars)) ⊆
    (((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof).resolve
    ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) var (Finset.sdiff_subset h_4 : var ∈ vars)) := by
    exact
      resolve_subsets var vars (p_1.unsubstitute_rhs ρ h_subset) (p_2.unsubstitute_rhs ρ h_subset)
        ((c_2.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
        ((c_3.combine ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
        (Finset.sdiff_subset h_4) idea₁ idea₂

  exact Finset.card_le_card inter_idea
  trans Finset.card c_1 + Finset.card sub_vars
  trans Finset.card ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof)
  have temp₁ : Finset.disjUnion (vars \ sub_vars) sub_vars (Finset.sdiff_disjoint : Disjoint (vars \ sub_vars) sub_vars) = vars := by
    aesop

  have idea₃ : ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ⊆
    ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ∪ {var.toLiteral var_incl} := by
    exact inter_idea_new_version vars sub_vars (var.toLiteral h_4) ρ c_1 c_2 inter_proof var_incl left

  have idea₄ : ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ⊆
    ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars inter_proof) ∪ {var.toNegLiteral var_incl} := by
    exact inter_idea_new_version vars sub_vars (var.toNegLiteral h_4) ρ c_1 c_3 inter_proof var_incl right

  simp only [ge_iff_le]

  apply resolve_subsets_trick var vars ((Clause.combine c_1 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
    ((Clause.combine c_2 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
    ((Clause.combine c_3 ρ.toClause Finset.sdiff_disjoint).convert_trivial vars temp₁)
    (by grind) idea₃ idea₄
  exact card_combination c c_1
  simp_all only [add_le_add_iff_right, le_sup_left]


lemma resolve_width_case (vars sub_vars) (φ : CNFFormula vars) (var : Variable)
    (ρ : Assignment sub_vars) (c c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (c₁ c₂ : Clause vars)
    (π₁ : TreeLikeResolution φ c₁)
    (π₂ : TreeLikeResolution φ c₂)
    (left : c_2 ⊆ c_1 ∪ {var.toLiteral h_4})
    (right : c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})
    (v : Variable)
    (h_v_mem_vars : v ∈ vars)
    (h_v_not_mem_c : v ∉ ((TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪
      {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset).variables)
    (left_1 : c₁ ⊆ (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧
      c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset ∪ {v.toLiteral h_v_mem_vars})
    (right_1 : c₂ ⊆
      (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧
      c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset ∪ {v.toNegLiteral h_v_mem_vars})
    (heq : (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute ρ h_subset =
      TreeLikeResolution.resolve c₁ c₂ v h_v_mem_vars h_v_not_mem_c π₁ π₂ (⟨left_1, right_1⟩ : c₁ ⊆ (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2
      (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})).unsubstitute_rhs ρ h_subset ∪ {v.toLiteral h_v_mem_vars} ∧
      c₂ ⊆
      (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2 (⟨left, right⟩ : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4}
      )).unsubstitute_rhs ρ h_subset ∪ {v.toNegLiteral h_v_mem_vars}))
    (h_2 : (p_1.unsubstitute ρ h_subset).width ≤ p_1.width + Finset.card sub_vars)
    (h_3 : (p_2.unsubstitute ρ h_subset).width ≤ p_2.width + Finset.card sub_vars):
    (π₁.width ≤ max (Finset.card c_1) (max p_1.width p_2.width) + Finset.card sub_vars) ∧
      (π₂.width ≤ max (Finset.card c_1) (max p_1.width p_2.width) + Finset.card sub_vars)
    := by

    constructor

    trans p_1.width + Finset.card sub_vars
    trans (p_1.unsubstitute ρ h_subset).width
    unfold TreeLikeResolution.unsubstitute at heq
    simp at heq
    obtain ⟨heq₁, heq₂, heq₃, heq₄, heq₅⟩ := heq
    subst heq₁ heq₂ heq₃
    simp_all only [heq_eq_eq, Finset.union_singleton, le_refl]
    exact h_2
    simp

    trans p_2.width + Finset.card sub_vars
    trans (p_2.unsubstitute ρ h_subset).width
    unfold TreeLikeResolution.unsubstitute at heq
    simp at heq
    obtain ⟨heq₁, heq₂, heq₃, heq₄, heq₅⟩ := heq
    subst heq₁ heq₂ heq₃
    simp_all only [heq_eq_eq, Finset.union_singleton, le_refl]
    exact h_3
    simp



lemma induction_step_width_incr {vars sub_vars} {φ : CNFFormula vars} {var : Variable}
    {ρ : Assignment sub_vars} (c c_1 c_2 c_3 : Clause (vars \ sub_vars))
    (h_subset : sub_vars ⊆ vars)
    (h_4 : var ∈ vars \ sub_vars) (h_0 : var ∉ c_1.variables)
    (p_1 : TreeLikeResolution (φ.substitute ρ) c_2)
    (p_2 : TreeLikeResolution (φ.substitute ρ) c_3)
    (h_1 : c_2 ⊆ c_1 ∪ {var.toLiteral h_4} ∧ c_3 ⊆ c_1 ∪ {var.toNegLiteral h_4})
    (h_2 : (p_1.unsubstitute ρ h_subset).width ≤ p_1.width + Finset.card sub_vars)
    (h_3 : (p_2.unsubstitute ρ h_subset).width ≤ p_2.width + Finset.card sub_vars) :
    ((TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2 h_1).unsubstitute ρ h_subset).width ≤
    (TreeLikeResolution.resolve c_2 c_3 var h_4 h_0 p_1 p_2 h_1).width + Finset.card sub_vars := by
  unfold TreeLikeResolution.width
  obtain ⟨left, right⟩ := h_1
  split
  next x x_1 h_c_in_φ heq =>
    exact resolve_ineq vars sub_vars φ var ρ c c_1 c_2 c_3 h_subset h_4 h_0 p_1 p_2 left right
  next x x_1 c₁ c₂ v h_v_mem_vars π₁ π₂ h_v_not_mem_c h_resolve
    heq =>
    simp_all only [sup_le_iff]
    obtain ⟨left_1, right_1⟩ := h_resolve
    apply And.intro
    · exact resolve_ineq vars sub_vars φ var ρ c c_1 c_2 c_3 h_subset h_4 h_0 p_1 p_2 left right
    · apply resolve_width_case vars sub_vars φ
          var ρ c c_1 c_2 c_3 h_subset h_4 h_0 p_1
          p_2 c₁ c₂ π₁ π₂ left right v h_v_mem_vars h_v_not_mem_c
          left_1 right_1 heq h_2 h_3



lemma unsub_increase_width {vars sub_vars} {φ : CNFFormula vars}
    {ρ : Assignment sub_vars} (c : Clause (vars \ sub_vars))
    (π : TreeLikeResolution (φ.substitute ρ) c) (h_subset : sub_vars ⊆ vars) :
    (π.unsubstitute ρ h_subset).width ≤ π.width + sub_vars.card := by
  induction π
  case axiom_clause C h =>
    unfold TreeLikeResolution.unsubstitute
    simp_all only
    unfold TreeLikeResolution.width
    trans ((Clause.combine C ρ.toClause Finset.sdiff_disjoint).convert_trivial vars (by aesop)).card
    · refine Finset.card_le_card ?_
      · exact TreeLikeResolution.unsubstitute_rhs_variables ρ
          (TreeLikeResolution.axiom_clause h) h_subset
    exact card_combination c C
  case resolve c_1 c_2 c_3 var h_4 h_0 p_1 p_2 h_1 h_2 h_3 =>
    exact induction_step_width_incr c_2 c_1 c_2 c_3 h_subset h_4 h_0 p_1 p_2 h_1 h_2 h_3


lemma var_unsub_increase_width {vars} {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ : Assignment {x.variable}) (c : Clause (vars \ {x.variable}))
    (π : TreeLikeResolution (φ.substitute ρ) c) :
    (π.unsubstitute ρ (by exact Finset.singleton_subset_iff.mpr h₀)).width ≤ π.width + 1 := by
  have : {x.variable} ⊆ vars := by
    exact Finset.singleton_subset_iff.mpr h₀
  trans π.width + ({x.variable} : Finset Variable).card
  · exact unsub_increase_width c π (Finset.singleton_subset_iff.mpr h₀)
  · exact Nat.le_refl (π.width + ({x.variable} : Finset Variable).card)

-- Managed to vibe code it succesfully!

open Classical -- Necessary to use 'choose'

lemma width_closure {vars} (φ₁ φ₂ : CNFFormula vars) (W : ℕ) (C_0 : Clause vars)
    (h_all : ∀ C ∈ φ₂, ∃ (π : TreeLikeResolution φ₁ C), π.width ≤ W)
    (h_once : ∃ (π_1 : TreeLikeResolution φ₂ C_0), π_1.width ≤ W) :
    ∃ π' : TreeLikeResolution φ₁ C_0, π'.width  ≤ W := by

  obtain ⟨π₁, hπ₁⟩ := h_once

  -- 1. Extract the "Subtype" (Tree + Proof) for every axiom
  let T2_with_bound : ∀ {C}, C ∈ φ₂ → { π : TreeLikeResolution φ₁ C // π.width ≤ W } :=
    fun hC => ⟨choose (h_all _ hC), choose_spec (h_all _ hC)⟩

  -- 2. Define the recursive grafting
  let rec graft {c : Clause vars} (π : TreeLikeResolution φ₂ c) :
    { P : TreeLikeResolution φ₁ c // P.width ≤ max (π.width) W } :=
    match π with
    | .axiom_clause h_in =>
        let ⟨sub_tree, h_sub_w⟩ := T2_with_bound h_in
        ⟨sub_tree, by
          -- Logic: width π is just c.size here.
          -- Since c is an axiom, width sub_tree ≤ W, so width ≤ max(c.size, W)
          aesop ⟩

    | .resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
        let ⟨P₁, hP₁⟩ := graft π₁
        let ⟨P₂, hP₂⟩ := graft π₂
        let P_final := TreeLikeResolution.resolve c₁ c₂ v h_v_mem h_v_not P₁ P₂ h_res
        ⟨P_final, by
          -- Logic: width P_final is max(c.size, width P₁, width P₂)
          -- Use hP₁ and hP₂ to show this is ≤ max (width T1) W
          unfold TreeLikeResolution.width
          simp
          grind⟩

  -- Execute the recursion on T1 to produce the final proof P
  let X := graft π₁

  obtain ⟨π₁', hπ₁'⟩ := X
  use π₁'
  aesop


lemma trivial_subs_unfold {vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (h_1 : ∀ l ∈ ρ_true.toClause, l.variable ∈ vars):
    (ρ_true.toClause).convert vars h_1 = ({x.negate} : Clause vars) := by
  cases x
  case neg v_1 hv =>
    have idea_2 : ρ_true (Literal.pos v_1 hv).variable (by aesop) = false := by
      aesop
    unfold Assignment.toClause
    unfold Clause.convert
    unfold Assignment.negVariable
    aesop
  case pos v_1 hv =>
    have idea_2 : ρ_true (Literal.pos v_1 hv).variable (by aesop) = true := by
      aesop
    unfold Assignment.toClause
    unfold Clause.convert
    unfold Assignment.negVariable
    aesop



lemma ufold_one_literal {vars} {φ : CNFFormula vars}
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (π_1 : TreeLikeRefutation (φ.substitute ρ_true))
    (fact₀ : {x.variable} ⊆ vars) :
    (TreeLikeResolution.unsubstitute_rhs ρ_true π_1 fact₀) ⊆ ({x.negate} : Clause vars) := by

  unfold TreeLikeRefutation at π_1

  have trick :  Finset.disjUnion (vars \ {x.variable}) {x.variable}
      (Finset.sdiff_disjoint : Disjoint (vars \ {x.variable}) {x.variable}) = vars := by
    aesop

  have : (π_1.unsubstitute_rhs ρ_true fact₀) ⊆
      (Clause.combine (BotClause (vars \ {x.variable})) ρ_true.toClause
      Finset.sdiff_disjoint).convert_trivial vars trick := by
    exact TreeLikeResolution.unsubstitute_rhs_variables ρ_true π_1 fact₀

  trans ((BotClause (vars \ {x.variable})).combine ρ_true.toClause
      (Finset.sdiff_disjoint : Disjoint (vars \ {x.variable}) {x.variable})).convert_trivial vars trick

  exact this

  have trick₁ : ∀ l ∈ ρ_true.toClause, l.variable ∈ vars := by
    aesop

  have idea : (ρ_true.toClause).convert vars trick₁ = ({x.negate} : Clause vars):= by
    exact trivial_subs_unfold x h₀ ρ_true h_value trick₁

  rw[<-idea]

  unfold BotClause

  unfold Clause.combine
  simp
  unfold Clause.convert_trivial
  aesop


def convert_proof (W : ℕ) {vars₁ vars₂ : Variables} {φ : CNFFormula vars₁} {C : Clause vars₁}
  {φ₁ : CNFFormula vars₂} (h_subs : vars₁ ⊆ vars₂)
  (h_conv : (CNFFormula.simple_convert vars₁ vars₂ φ h_subs) = φ₁)
  (π₁ : TreeLikeResolution φ C)
  (h_width : π₁.width ≤ W) :
  { π₂ : TreeLikeResolution φ₁
  (C.convert vars₂ (by exact fun l a ↦
    subset_of_vars_clause vars₁ vars₂ C h_subs l a)) // π₂.width ≤ W } :=

  have idea : ∀ c : Clause vars₁, (∀ l ∈ c, l.variable ∈ vars₂) := by
    intro c l a
    subst h_conv
    apply h_subs
    simp_all only [Literal.variable_mem_vars]


  have idea' : Finset.card C ≤ W := by
    induction π₁
    subst h_conv
    exact h_width
    rename_i h_resolve π₁_ih π₂_ih
    subst h_conv
    obtain ⟨left, right⟩ := h_resolve
    unfold TreeLikeResolution.width at h_width
    simp_all only [Finset.union_singleton, sup_le_iff]

  match π₁ with
  -- CASE 1: The proof is just an axiom
  | .axiom_clause h_in =>
      let C_new := C.convert vars₂ (by exact fun l a ↦ idea C l a)
        have : C_new ∈ φ₁ := by
          rw[<-h_conv]
          unfold CNFFormula.simple_convert
          aesop
        let π₂ := TreeLikeResolution.axiom_clause (by
        -- Prove that C_new is in the converted formula
        -- This follows from the definition of CNFFormula.simple_convert
          exact this)
        ⟨π₂, by
        -- Width of an axiom is the size of the clause.
        -- Since convert doesn't change the number of literals, width remains the same.
          unfold TreeLikeResolution.width
          aesop ⟩

  -- CASE 2: The proof is a resolution step
  | .resolve c₁ c₂ v h_v_mem h_v_not π_a π_b h_res =>
      -- 1. Recursively convert the sub-proofs
      -- (You need to split the width bound h_width into bounds for π_a and π_b)
      have idea₁ : π_a.width ≤ W := by
        unfold TreeLikeResolution.width at h_width
        subst h_conv
        simp_all only [Finset.union_singleton, sup_le_iff, true_and]
      have idea₂ : π_b.width ≤ W := by
        unfold TreeLikeResolution.width at h_width
        subst h_conv
        simp_all only [Finset.union_singleton, sup_le_iff, true_and]

      let ⟨π_a_new, h_wa⟩ := convert_proof W h_subs h_conv π_a idea₁
        -- width π₁ = max |C| (max (width π_a) (width π_b)), so width π_a ≤ width π₁


      let ⟨π_b_new, h_wb⟩ := convert_proof W h_subs h_conv π_b idea₂

      -- 2. Lift the resolution variable to the new context
      let v_new_mem := h_subs h_v_mem

      have fact₁ : ∀ l ∈ c₁, l.variable ∈ vars₂ := by
        exact fun l a ↦ idea c₁ l a

      have fact₂ : ∀ l ∈ c₂, l.variable ∈ vars₂ := by
        exact fun l a ↦ idea c₂ l a

      have fact₀ :  ∀ l ∈ C, l.variable ∈ vars₂ := by
        exact fun l a ↦ idea C l a

      have fact₄ : v ∉ (C.convert vars₂ fact₀).variables := by
        aesop

      have left : c₁ ⊆ C ∪ {v.toLiteral h_v_mem} := by
        exact h_res.left

      have right : c₂ ⊆ C ∪ {v.toNegLiteral h_v_mem} := by
        exact h_res.right

      have h_resolve : c₁.convert vars₂ fact₁ ⊆ C.convert vars₂ fact₀ ∪ {v.toLiteral v_new_mem} ∧
        c₂.convert vars₂ fact₂ ⊆ C.convert vars₂ fact₀ ∪ {v.toNegLiteral v_new_mem} := by
        constructor
        have incl₁ : ∀ l ∈ C ∪ {v.toLiteral h_v_mem}, l.variable ∈ vars₂ := by
          exact fun l a ↦ idea (C ∪ {v.toLiteral h_v_mem}) l a
        have incl₂ : ∀ l ∈ ({v.toLiteral h_v_mem} : Clause vars₁), l.variable ∈ vars₂ := by
          exact fun l a ↦ idea {v.toLiteral h_v_mem} l a
        trans (C ∪ ({v.toLiteral h_v_mem} : Clause vars₁)).convert vars₂ incl₁
        exact loose_convert c₁ (C ∪ {v.toLiteral h_v_mem}) left
        trans C.convert vars₂ fact₀ ∪ ({v.toLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂
        have new₁ : (C ∪ {v.toLiteral h_v_mem}).convert vars₂ incl₁ = C.convert vars₂ fact₀ ∪ ({v.toLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ := by
          exact carry_through_convert_expl vars₁ vars₂ C ({v.toLiteral h_v_mem} : Clause vars₁) incl₁ fact₀  incl₂
        exact Finset.subset_of_eq new₁
        have new₂ : ({v.toLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ = {v.toLiteral v_new_mem} := by
          unfold Clause.convert
          simp
          subst h_conv
          simp_all only [Clause.convert_keeps_variables, not_false_eq_true, Finset.union_singleton, Finset.mem_insert,
            forall_eq_or_imp, Finset.mem_singleton, implies_true, and_self]
          obtain ⟨left_1, right_1⟩ := h_res
          ext a : 1
          simp_all only [Finset.mem_filterMap, Finset.mem_singleton, Option.dite_none_right_eq_some,
            Option.some.injEq, and_exists_self, exists_prop_eq]
          apply Iff.intro
          · intro a_1
            subst a_1
            rfl
          · intro a_1
            subst a_1
            rfl
        rw [new₂]


        have incl₁ : ∀ l ∈ C ∪ {v.toNegLiteral h_v_mem}, l.variable ∈ vars₂ := by
          exact fun l a ↦ idea (C ∪ {v.toNegLiteral h_v_mem}) l a
        have incl₂ : ∀ l ∈ ({v.toNegLiteral h_v_mem} : Clause vars₁), l.variable ∈ vars₂ := by
          exact fun l a ↦ idea {v.toNegLiteral h_v_mem} l a
        trans (C ∪ ({v.toNegLiteral h_v_mem} : Clause vars₁)).convert vars₂ incl₁
        exact loose_convert c₂ (C ∪ {v.toNegLiteral h_v_mem}) right
        trans C.convert vars₂ fact₀ ∪ ({v.toNegLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂
        have new₁ : (C ∪ {v.toNegLiteral h_v_mem}).convert vars₂ incl₁ = C.convert vars₂ fact₀ ∪ ({v.toNegLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ := by
          exact carry_through_convert_expl vars₁ vars₂ C ({v.toNegLiteral h_v_mem} : Clause vars₁) incl₁ fact₀  incl₂
        subst h_conv
        simp_all only [Clause.convert_keeps_variables, not_false_eq_true, Finset.union_singleton, subset_refl]
        have new₂ : ({v.toNegLiteral h_v_mem} : Clause vars₁).convert vars₂ incl₂ = {v.toNegLiteral v_new_mem} := by
          unfold Clause.convert
          simp
          subst h_conv
          simp_all only [Clause.convert_keeps_variables, not_false_eq_true, Finset.union_singleton, Finset.mem_insert,
            forall_eq_or_imp, Finset.mem_singleton, implies_true, and_self]
          obtain ⟨left_1, right_1⟩ := h_res
          ext a : 1
          simp_all only [Finset.mem_filterMap, Finset.mem_singleton, Option.dite_none_right_eq_some,
            Option.some.injEq, and_exists_self, exists_prop_eq]
          apply Iff.intro
          · intro a_1
            subst a_1
            rfl
          · intro a_1
            subst a_1
            rfl
        rw [new₂]


      -- 3. Construct the new resolution node
      let π_new := TreeLikeResolution.resolve
        (c₁.convert vars₂ fact₁)
        (c₂.convert vars₂ fact₂)
        v v_new_mem fact₄ π_a_new π_b_new h_resolve

      ⟨π_new, by
        -- width is max of |C_new| and the sub-widths.
        -- All these are ≤ W because the original ones were.
        unfold TreeLikeResolution.width
        aesop⟩

-- Tried to vibe code this one - ended up horribly...

lemma width_respect_convert (vars₁ vars₂) (φ : CNFFormula vars₁)
   (φ₁ : CNFFormula vars₂) (h_subs : vars₁ ⊆ vars₂)
   (h_conv : (CNFFormula.simple_convert vars₁ vars₂ φ h_subs) = φ₁)
   (W : ℕ) (C : Clause vars₁)
   (π_1 : TreeLikeResolution φ C) (h_width_true : π_1.width ≤ W) :
   ∃ (π_2 : TreeLikeResolution φ₁ (C.convert vars₂
    (by exact fun l a ↦
    subset_of_vars_clause vars₁ vars₂ C h_subs l a))), π_2.width ≤ W  := by
  let ⟨π, h⟩ := convert_proof W h_subs h_conv π_1 h_width_true
  exact ⟨π, h⟩


lemma width_combine {vars} {φ : CNFFormula vars}
    (h_unsat : Unsat φ) (x : Literal vars) (h₀ : x.variable ∈ vars)
    (ρ_true : (Assignment ({x.variable} : Finset Variable)))
    (h_value : ρ_true = (fun _ _ => (x.polarity : Bool)))
    (ρ_false : (Assignment ({x.variable} : Finset Variable)))
    (h_value_false : ρ_true = (fun _ _ => (¬x.polarity : Bool)))
    (W : ℕ) (π_1 : TreeLikeRefutation (φ.substitute ρ_true)) (h_width_true : π_1.width ≤ W)
    (π_2 : TreeLikeRefutation (φ.substitute ρ_false)) (h_width_false : π_2.width ≤ W + 1) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W + 1:= by

  have fact₀ : {x.variable} ⊆ vars := by
    exact Finset.singleton_subset_iff.mpr h₀

  let π_1_unfolded := TreeLikeResolution.unsubstitute ρ_true π_1 fact₀

  have idea₀ : (TreeLikeResolution.unsubstitute_rhs ρ_true π_1 fact₀) ⊆ ({x.negate}) := by
    exact ufold_one_literal x h₀ ρ_true h_value π_1 fact₀

  have idea₁ : π_1_unfolded.width ≤ W + 1 := by
    trans π_1.width + ({x.variable} : Finset Variable).card
    exact unsub_increase_width (BotClause (vars \ {x.variable})) π_1 fact₀
    trans TreeLikeResolution.width π_1 + 1
    exact Nat.le_refl (TreeLikeResolution.width π_1 + ({x.variable} : Finset Variable).card)
    exact Nat.add_le_add_right h_width_true 1


  have fact₁ : (C : Clause (vars \ {x.variable})) -> (∀ l ∈ C, l.variable ∈ vars) := by
    intro C l h'
    have : l.variable ∈ (vars \ {x.variable}) := by
      exact subset_of_vars_clause (vars \ {x.variable}) (vars \ {x.variable}) C (fun ⦃a⦄ a_1 ↦ a_1) l h'
    simp_all only [Literal.variable_mem_vars, Finset.mem_sdiff, Finset.mem_singleton, π_1_unfolded]

  --let C' := (φ.substitute ρ_false).convert vars

  have idea₂ : ∀ C ∈ (φ.substitute ρ_false), ∃ (π : TreeLikeResolution φ
    (C.convert vars (by exact fun l a ↦ fact₁ C l a))), π.width ≤ W := by
    sorry


  sorry


theorem width_imply_size {vars} {φ : CNFFormula vars}
    (h_unsat : Unsat φ) (π : TreeLikeRefutation φ) (W : ℕ) (h_size : π.size ≤ 2 ^ W) :
    ∃ (π' : TreeLikeRefutation φ), π'.width ≤ W := by
  sorry
