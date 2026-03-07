import BSWLean.Treelike

def is_resolve {vars} {φ : CNFFormula vars} {c : Clause vars} :
    TreeLikeResolution φ c → Prop
  | .axiom_clause _ => false
  | .resolve .. => true

def IsRegularRes {vars} {φ : CNFFormula vars} : ∀ {c : Clause vars}, TreeLikeResolution φ c → Prop
  | _, .axiom_clause _ => True
  | _, .resolve c₁ c₂ v _ _ π₁ π₂ _ =>
      v ∈ c₁.variables ∧ v ∈ c₂.variables ∧ IsRegularRes π₁ ∧ IsRegularRes π₂


@[simp]
lemma trivial_convert_card {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert_trivial vars₂ h).card = C.card := by
  refine Set.BijOn.finsetCard_eq ?_ ?_
  · intro lit₁
    subst h
    exact lit₁
  subst h
  simp_all only
  constructor
  · unfold Clause.convert_trivial
    unfold Clause.convert
    simp only [Literal.convert_self, dite_eq_ite, Finset.coe_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, and_self_left, exists_eq_right,
      SetLike.setOf_mem_eq]
    exact fun ⦃x⦄ a ↦ a
  unfold Clause.convert_trivial
  unfold Clause.convert
  simp
  refine Finset.surjOn_of_injOn_of_card_le (fun lit₁ ↦ lit₁) (fun ⦃x⦄ a ↦ a) ?_ ?_
  · exact Function.Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a
  · exact (Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a_1 ↦ a_1).mpr rfl

@[simp]
lemma filterMap_card {α β} [DecidableEq α] [DecidableEq β] (s : Finset α) {f : α → Option β} {h} :
    Finset.card (s.filterMap f h) ≤ Finset.card s := by
  induction s using Finset.induction_on
  case empty =>
    rfl
  case insert a s' h_a ih =>
    have : (insert a s').card = s'.card + 1 := by
      exact Finset.card_insert_of_notMem h_a
    rw [this]
    trans (Finset.filterMap f s' h).card + 1
    swap
    · simp [ih]
    let b : Finset β := if h : (f a).isSome then {(f a).get h} else ∅
    have : b.card ≤ 1 := by aesop
    trans ((Finset.filterMap f s' h) ∪ b).card
    swap
    · simp_all only [b]
      split
      next h_1 =>
        grind
      next h_1 =>
        simp_all
    refine (Finset.eq_iff_card_ge_of_superset ?_).mpr ?_
    · grind
    · grind


lemma convert_card_ineq {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert vars₂ h).card ≤  C.card := by
  unfold Clause.convert
  exact filterMap_card C

lemma convert_card_ineq_oppsite {vars₁ vars₂} {C : Clause vars₁} {h}
  : (C.convert vars₂ h).card ≥ C.card := by
    have h₂ : ∀ l ∈ (C.convert vars₂ h), l.variable ∈ vars₁ := by
      intro l a
      unfold Clause.convert at a
      simp at a
      obtain ⟨w, h_1⟩ := a
      obtain ⟨w_1, h_1⟩ := h_1
      subst h_1
      simp_all only [Literal.convert_variable, Literal.variable_mem_vars]
    have idea₁ : ((C.convert vars₂ h).convert vars₁ h₂).card ≤ (C.convert vars₂ h).card := by
      exact convert_card_ineq
    simp_all

@[simp]
lemma convert_card {vars₁ vars₂} {C : Clause vars₁} {h} :
    (C.convert vars₂ h).card = C.card := by
  refine Nat.le_antisymm ?_ ?_
  · exact convert_card_ineq
  · exact convert_card_ineq_oppsite



lemma to_clause_card_less_than_sub_vars_card {sub_vars : Variables} (ρ : Assignment sub_vars) :
  (Finset.card ρ.toClause ≤ Finset.card sub_vars) := by
  unfold Assignment.toClause
  exact filterMap_card sub_vars

lemma disjoint_contradiction {α} [DecidableEq α] (s₁ s₂ : Finset α) (h_disj : Disjoint s₁ s₂)
    (h : ∃ x ∈ s₁, x ∈ s₂) : False := by
  rw [Finset.disjoint_iff_inter_eq_empty] at h_disj
  obtain ⟨x, h_x_in_s₁, h_x_in_s₂⟩ := h
  have : x ∈ s₁ ∩ s₂ := by
    simp only [Finset.mem_inter]
    constructor
    · assumption
    · assumption
  rw [h_disj] at this
  contradiction

@[simp]
lemma subset_combine {vars₁ vars₂} (c₁ c₂ : Clause vars₁) (c' : Clause vars₂)
    (h_disj : Disjoint vars₁ vars₂) :
    (Clause.combine c₁ c' h_disj) ⊆ (Clause.combine c₂ c' h_disj) ↔ c₁ ⊆ c₂ := by
  unfold Clause.combine
  simp only
  constructor
  case mpr =>
    intro h_subset
    refine Finset.union_subset_union_left ?_
    aesop
  case mp =>
    intro h_subset
    have : c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ⊆
           c₂.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) := by
      rw [Finset.union_subset_iff] at h_subset
      replace h_subset := h_subset.1
      intro l h_l_in_c₁
      have h_apply_subset : l ∈ c₂.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∪
                                c'.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) := by
        apply h_subset
        assumption
      simp only [Finset.mem_union] at h_apply_subset
      by_contra!
      simp_all only [false_or]
      have h_l_in_vars₁ : l.variable ∈ vars₁ := by
        have : l.variable ∈
            (c₁.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop)).variables := by
          exact literal_in_clause_variables h_l_in_c₁
        rw [Clause.convert_keeps_variables] at this
        have h₁ : c₁.variables ⊆ vars₁ := by aesop
        aesop
      have h_l_in_vars₂ : l.variable ∈ vars₂ := by
        have : l.variable ∈
            (c'.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop)).variables := by
          exact literal_in_clause_variables (by assumption)
        rw [Clause.convert_keeps_variables] at this
        have h₁ : c'.variables ⊆ vars₂ := by aesop
        aesop
      have : l.variable ∈ vars₁ ∩ vars₂ := by aesop
      unfold Disjoint at h_disj
      apply disjoint_contradiction vars₁ vars₂ h_disj
      use l.variable

    intro l h_l_in_c₁
    have h_l_in_c_convert : l.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) ∈
        c₂.convert (Finset.disjUnion vars₁ vars₂ h_disj) (by aesop) := by
      apply this
      aesop

    simp_all




lemma resolution_restrict {vars₁ vars₂ : Variables} {φ : CNFFormula vars₂}
    (h_subs : vars₁ ⊆ vars₂) (ρ : Assignment vars₁)
    {C : Clause vars₂} (π : TreeLikeResolution φ C) :
    (C.substitute ρ = none) ∨
    (∃ c_res, C.substitute ρ = some c_res ∧
      ∃ c', c' ⊆ c_res ∧
      ∃ (π' : TreeLikeResolution (φ.substitute ρ) c'),
        π'.width ≤ π.width ∧ π'.size ≤ π.size) := by
  induction π with
  | axiom_clause h_in =>
      -- Look at c.substitute ρ.
      -- If none, return Or.inl.
      -- If some c_res, c_res is in the new formula by definition of CNFFormula.substitute.
      unfold Clause.substitute
      sorry
  | resolve c₁ c₂ v h_v_mem h_v_not_mem π₁ π₂ h_res ih₁ ih₂ =>
      -- Check if v ∈ vars₁ (assigned) or v ∉ vars₁ (unassigned).
      -- If assigned, one of ih₁ or ih₂ will evaluate to `none`, and the other
      -- will shrink and bypass the resolution step entirely!
      -- If unassigned, apply resolution to the results of ih₁ and ih₂.
      sorry

-- lemma width_and_size_respect_substitution {vars₁ vars₂ : Variables} {φ : CNFFormula vars₂}
--     (x : Literal vars₂) (h₀ : x.variable ∈ vars₂) (h_subs : vars₁ ⊆ vars₂)
--     (ρ : (Assignment vars₁))
--     (W : ℕ) (S : ℕ)
--     (π : TreeLikeResolution φ (BotClause vars₂)) (h_width : π.width ≤ W) (h_size : π.size ≤ S) :
--     ∃ (π_1 : TreeLikeResolution (φ.substitute ρ) (BotClause (vars₂ \ vars₁))), (π_1.width ≤ W ∧ π_1.size ≤ S) := by

--   -- 1. Apply the generalized induction lemma
--   have h_gen := resolution_restrict h_subs ρ π

--   -- 2. Handle the two cases from the generalized lemma
--   rcases h_gen with h_none | ⟨c_res, h_some, c', h_subset, π', h_w, h_s⟩

--   · -- Case 1: BotClause was satisfied (Impossible)
--     -- You will need a helper lemma: `BotClause.substitute ρ ≠ none`
--     -- Once you have it, this branch closes by contradiction.
--     sorry

--   · -- Case 2: We got a restricted proof
--     -- You need a helper lemma showing that `BotClause.substitute ρ = some (BotClause (vars₂ \ vars₁))`
--     -- From `h_some`, you can deduce `c_res = BotClause (vars₂ \ vars₁)`
--     -- From `h_subset`, `c' ⊆ BotClause (vars₂ \ vars₁)`, meaning `c' = BotClause (vars₂ \ vars₁)`


--     have : c' = BotClause (vars₂ \ vars₁) :=
--       sorry
--     subst c'
--     -- Once you rewrite c' to BotClause, π' is exactly the TreeLikeRefutation you need!
--     use π'  -- Wait to do this until Lean sees π' derives BotClause

--     -- Prove the bounds using transitivity
--     constructor
--     · exact Nat.le_trans h_w h_width
--     · exact Nat.le_trans h_s h_size


lemma substitute_trivial_property {vars}
    (φ : CNFFormula vars)
    (x : Literal vars) (h₀ : x.variable ∈ vars)
    (C_0 : Clause vars)
    (h_subs : (vars \ {x.variable}) ⊆ vars)
    (ρ_false : (Assignment ({x.variable} : Finset Variable)))
    (h_value_false : ρ_false = (fun _ _ => (¬x.polarity : Bool)))
    (h_c : C_0 ∈ ((CNFFormula.simple_convert
        (vars \ {x.variable}) vars (φ.substitute ρ_false) h_subs)))
    (C_1 : Clause (vars \ {x.variable}))
    (h_C_1_conv_left : C_1 ∈ (φ.substitute ρ_false))
    (h_incl : ∀ l ∈ C_1, l.variable ∈ vars)
    (h_C_1_conv_right : C_1.convert vars h_incl = C_0)
    (C_2 : Clause vars)
    (h_C_2_conv : C_2 ∈ φ ∧ C_2.substitute ρ_false = some C_1)
    : C_2 ⊆ C_0 ∪ ({x} : Clause vars) := by
  intro l hl

  obtain ⟨left, right⟩ := h_C_2_conv
  rw [← h_C_1_conv_right]


  -- 3. Since l ∈ C_1.convert, there must be a source literal l' ∈ C_1
  -- You'll likely need to unfold Clause.convert or use a lemma like 'mem_convert'
  unfold Clause.convert
  simp
  by_cases l = x
  case pos h_l =>
    exact Or.symm (Or.inr h_l)
  case neg h_l =>
    refine Or.symm (Or.intro_left (l = x) ?_)
    unfold Clause.substitute at right
    simp at right
    obtain ⟨h_sp_l, h_sp_r⟩ := right
    -- aesop
    -- unfold Clause.split
    -- aesop
    -- unfold Clause.shrink
    -- aesop
    -- unfold Clause.split at h_c
    -- aesop
    -- unfold Clause.shrink at h_c
    -- aesop
    -- unfold Clause.convert at h_c
    -- simp at h_c
    sorry

lemma weaken_proof {vars} {φ : CNFFormula vars} {c c' : Clause vars}
    (π : TreeLikeResolution φ c) (h_sub : c ⊆ c') :
    ∃ (π' : TreeLikeResolution φ c'), IsRegularRes π → (IsRegularRes π' ∧ π'.size ≤ π.size) := by
  -- This requires its own induction on π.
  -- If you encounter a resolve node where the resolved variable is already in c',
  -- you must bypass that node here as well to maintain IsRegularRes.
  induction π with
  | axiom_clause h_in =>
      -- Base case is trivially regular
      sorry
      -- use TreeLikeResolution.axiom_clause h_in
      -- simp [IsRegularRes, TreeLikeResolution.size]
      -- sorry
  | resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ => sorry

lemma eliminate_vacuous_resolutions_prep {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c):
    ∃ (c' : Clause vars) (π' : TreeLikeResolution φ c'), (c' ⊆ c) ∧ IsRegularRes π' ∧ π'.size ≤ π.size := by
  induction π with
  | axiom_clause h_in =>
      -- Base case is trivially regular
      -- use .axiom_clause h_in
      -- simp [IsRegularRes, TreeLikeResolution.size]
      sorry
  | resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res ih₁ ih₂ =>
      -- 1. Extract the regularized subproofs from the inductive hypotheses
      -- obtain ⟨π₁', h_reg₁, h_size₁⟩ := ih₁
      -- obtain ⟨π₂', h_reg₂, h_size₂⟩ := ih₂

      -- -- 2. Check if the resolution is vacuous
      -- by_cases hv1 : v ∈ c₁.variables
      -- · by_cases hv2 : v ∈ c₂.variables
      --   · -- Case A: Non-vacuous. Both contain v.
      --     -- We can safely reconstruct the resolve node.
      --     use .resolve c₁ c₂ v h_v_mem h_v_not π₁' π₂' h_res

      --     -- The size and regularity bounds hold by simple arithmetic and the IHs
      --     constructor
      --     · simp only [IsRegularRes]
      --       exact ⟨hv1, hv2, h_reg₁, h_reg₂⟩
      --     · -- π'.size = 1 + π₁'.size + π₂'.size ≤ 1 + π₁.size + π₂.size
      --       -- (Use 'omega' or 'linarith' here)
      --       sorry

      --   · -- Case B: Vacuous on the right. v ∉ c₂.variables.
      --     -- Because c₂ ⊆ c ∪ {~v} and v ∉ c₂, it must be that c₂ ⊆ c.
      --     have h_c2_sub_c : c₂ ⊆ c := by
      --       -- Prove this using your Finset/Clause API
      --       sorry

      --     -- We completely bypass π₁' and the resolve node!
      --     obtain ⟨π_new, h_new_prop⟩ := weaken_proof π₂' h_c2_sub_c
      --     --use π_new

      --     -- π_new.size ≤ π₂'.size ≤ π₂.size < 1 + π₁.size + π₂.size
      --     -- (Apply h_new_prop to h_reg₂ to get regularity and size)
      --     sorry

      -- · -- Case C: Vacuous on the left. v ∉ c₁.variables.
      --   -- Exactly symmetrical to Case B.
      --   have h_c1_sub_c : c₁ ⊆ c := by
      --     sorry

      --   obtain ⟨π_new, h_new_prop⟩ := weaken_proof π₁' h_c1_sub_c
      --   --use π_new
      --   sorry
    sorry

@[aesop safe]
lemma proof_size_positive {vars} {φ : CNFFormula vars} {c : Clause vars}
    (π : TreeLikeResolution φ c) : π.size > 0 := by
  unfold TreeLikeResolution.size
  aesop

lemma size_one_proof {vars} (φ : CNFFormula vars)
    (W_c : ℕ) (h_clause_card : ∀ C ∈ φ, C.card ≤ W_c) (π : TreeLikeRefutation φ)
    (h_size : π.size ≤ 1) :
     π.width ≤ W_c := by
  cases h : π with
  | axiom_clause h_in => aesop
  | resolve c₁ c₂ v h_v_mem h_v_not π₁ π₂ h_res =>
      -- This is impossible, as a resolution step has size > 1.
      -- You can close this branch by contradiction.
    suffices π.size > 1 by
      omega

    unfold TreeLikeResolution.size at *
    subst h
    simp_all only [gt_iff_lt]
    trans 1 + π₁.size
    · aesop
    · aesop
