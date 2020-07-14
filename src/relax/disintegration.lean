/-
Copyright © 2020, Oracle and/or its affiliates. All rights reserved.
-/

import .relax

local attribute [instance] classical.prop_decidable

open set

namespace relax

variables (μ: probability_measure ℍ)

noncomputable
def maj_code (u: ℍ × ℍ): (ℍ × ℕ) :=
    let u1 := u.fst in
    let u2 := u.snd in
	let theta := generate_uniform_variate_simple(0,1,u1) in
	let X := generate_binomial_variate_simple(theta,u2) in
	(theta,X)

@[simp]
lemma measurable_maj_code:measurable ( λ (u: ℍ × ℍ),maj_code u) := 
begin
	unfold maj_code,
	simp,
	apply measurable.prod; simp,
	{
        apply measurable.comp,
        apply uniform_measurable,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable_fst,
        apply measurable_id,
	},
	{
		apply measurable.comp,
        apply binomial_measurable,
        apply measurable.prod; simp,
        apply measurable.comp,
        apply uniform_measurable,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable_fst,
        apply measurable_id,
        apply measurable_snd,      
        apply measurable_id,
	}
end

axiom τ(t: ℍ): probability_measure ℍ
axiom dd: ∀ t: ℍ, τ(t) {x: ℍ | generate_uniform_variate_simple(0,1,x) = t} = 1

noncomputable
def γ(t: ℍ): probability_measure (ℍ × ℕ) :=
	map maj_code (prod.prob_measure (τ(t)) μ)

def male_selected_(t: ℍ) := {v: (ℍ × ℕ)  | v.snd = 1 ∧ v.fst = t}

@[simp]
lemma is_measurable_1: is_measurable {v: (ℍ × ℕ) | v.snd = 1} :=
begin
    have prod: {v: (ℍ × ℕ) | v.snd = 1} = set.prod {x: ℍ | true} {n: ℕ | n = 1}, 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
        split, intro,
        split,
        rw mem_set_of_eq at *,
        trivial,
        rw mem_set_of_eq at *,
        exact a,
        intro,
        cases a,
        rw mem_set_of_eq at *,
        exact a_right,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,
    apply is_measurable.univ,
    trivial,
end

@[simp]
lemma is_measurable_2: ∀ t, is_measurable {v: (ℍ × ℕ) | v.fst = t} :=
begin
    intro,
    have prod: {v: (ℍ × ℕ) | v.fst = t} = set.prod {t} univ, 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
        split, intro,
        split,
        rw mem_set_of_eq at *,
        rw a, simp,
        rw mem_set_of_eq at *,
        trivial,
        intro,
        cases a,
        rw mem_set_of_eq at *,
        simp at a_left,
        exact a_left,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,  
    swap, apply is_measurable.univ,
    apply measure_theory.is_measurable_singleton,
end

lemma test:
	∀ t, (γ μ t) {a: ℍ × ℕ | a.fst = t} = 1 :=
begin
	intro,
	dunfold γ, 
	rw map_apply, simp,
	unfold maj_code, simp,
	have foo: {a: ℍ × ℍ | generate_uniform_variate_simple(0,1,a.fst) = t} = set.prod {a: ℍ | generate_uniform_variate_simple(0,1,a) = t} univ,
	{
		rw ext_iff,
		intros,
		repeat {rw mem_set_of_eq}, simp,
	},
	rw foo,
	rw prod.prob_measure_apply,
	rw dd, simp,
	simp,
	apply is_measurable.univ,
	simp,
	simp,
end

@[simp]
lemma is_measurable_3:
	∀ t, is_measurable {v: (ℍ × ℕ)  | v.snd = 1 ∧ v.fst = t} :=
begin
	intros,
	apply is_measurable.inter,
	apply is_measurable_1,
	apply is_measurable_2,
end

lemma rw_gamma_2:
	∀ t: ℍ, 
	(γ μ)(t) {a: ℍ × ℕ | a.snd = 1 ∧ a.fst = t} = t :=
begin
	intros,
	dunfold γ,
	rw map_apply; simp,
	have set_rw: {a: ℍ × ℍ | (maj_code a).snd = 1 ∧ (maj_code a).fst = t} = set.prod {a: ℍ | generate_uniform_variate_simple(0,1,a) = t} {a: ℍ | generate_binomial_variate_simple(t,a) = 1},
	{
		rw ext_iff,
		intros,
		repeat {rw mem_set_of_eq}, simp,
		cases x,
		unfold maj_code, simp,
	
		split; intros,
		{
			cases a,
			rw a_right at *, simp at *,
			assumption,
		},
		{
			cases a,
			rw a_left at *, simp at *,
			assumption,
		},		
	},
	rw set_rw, clear set_rw,
	rw prod.prob_measure_apply,

	have bin_rw:= generate_binomial_variate_simple_prop μ t,
	unfold E_bin at bin_rw,
	rw bin_rw at *, 

	rw dd,
	simp,

	simp,
	simp,
end

lemma maj_:
	∀ t: ℍ, 
	(γ μ)(t) (male_selected_ t) = t :=
begin
	intros,
	unfold male_selected_, 
	rw rw_gamma_2,
end

noncomputable
def code (u: (ℍ × ℕ) × ℍ × ℍ): (ℍ × ℕ) × (ℍ × ℕ) :=
    let theta := u.fst.fst in
    let X := u.fst.snd in
    let u3 := u.snd.fst in
	let u4 := u.snd.snd in
	let phi := generate_uniform_variate_simple(0.8 * theta,1,u3) in
	let Y := generate_binomial_variate_simple(phi,u4) in
	((theta,X),(phi,Y))

lemma measurable_coe : measurable (coe : nnreal → real) :=
begin
	apply measure_theory.measurable_of_continuous,
	apply nnreal.continuous_coe,
end

@[simp]
lemma measurable_code:measurable ( λ (u: (ℍ × ℕ) × ℍ × ℍ),code u) := 
begin
	unfold code, 
	apply measurable.prod,
	{
		apply measurable.prod; simp,
		{
			apply measurable.comp,
			apply measurable_fst,
			apply measurable_id,
			apply measurable.comp,
			apply measurable_fst,
			apply measurable_id,
			apply measurable_id,
		},
		{
			apply measurable.comp,
			apply measurable_snd,
			apply measurable_id,
			apply measurable.comp,
			apply measurable_fst,
			apply measurable_id,
			apply measurable_id,			
		},
	},
	{
		apply measurable.prod; simp,
		{
        	apply measurable.comp,
        	apply uniform_measurable,
        	apply measurable.prod; simp,
        	{
				apply measure_theory.measurable_mul,
				apply measurable_const,
				apply measurable.comp,
				apply measurable_coe,
				apply measurable_fst,
				apply measurable_fst,
				apply measurable_id,
			},
        	apply measurable.prod; simp,
        	apply measurable_const,
        	apply measurable_fst,
			apply measurable_snd,
        	apply measurable_id,
		},
		{
			apply measurable.comp,
        	apply binomial_measurable,
        	apply measurable.prod; simp,
        	apply measurable.comp,
        	apply uniform_measurable,
        	apply measurable.prod; simp,
        	{
				apply measure_theory.measurable_mul,
				apply measurable_const,
				apply measurable.comp,
				apply measurable_coe,
				apply measurable_fst,
				apply measurable_fst,
				apply measurable_id,
			},
        	apply measurable.prod; simp,
        	apply measurable_const,
        	apply measurable_fst,
			apply measurable_snd,  
        	apply measurable_id,
        	apply measurable_snd,  
			apply measurable_snd,      
        	apply measurable_id,			
		},
	}
end

noncomputable
def δ(t: ℍ): probability_measure ((ℍ × ℕ) × (ℍ × ℕ)) :=
    map code (prod.prob_measure ((γ μ)(t)) (prod.prob_measure μ μ))

@[simp]
lemma is_measurable_4: ∀ t, is_measurable {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.fst = t} :=
begin
    intro,
    have prod: {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.fst = t} = set.prod (set.prod {t} univ) (set.prod univ univ), 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
		rw mem_prod_eq,
        split, 
		{
			intro,
        	split,
			split,
        	rw mem_set_of_eq at *,
        	rw a, simp,
        	rw mem_set_of_eq at *,
        	trivial,
			rw mem_set_of_eq at *,
			simp,
		},
        intro,
        cases a,
        rw mem_set_of_eq at *,
        simp at a_left,
        exact a_left,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,  
	apply is_measurable_set_prod, 
	apply measure_theory.is_measurable_singleton,
    apply is_measurable.univ,
	apply is_measurable_set_prod, 
	apply is_measurable.univ,
	apply is_measurable.univ,
end

@[simp]
lemma is_measurable_5: is_measurable {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.snd = 1} :=
begin
    have prod: {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.snd = 1} = set.prod (set.prod univ {n: ℕ | n = 1}) (set.prod univ univ), 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
		rw mem_prod_eq,
        split, intro,
        split,
		split,
        rw mem_set_of_eq at *,
        trivial,
        rw mem_set_of_eq at *,
        exact a,
		split,
		rw mem_set_of_eq at *,
        trivial,
		rw mem_set_of_eq at *,
        trivial,
        intro,
        cases a,
		cases a_left,
        rw mem_set_of_eq at *,
        exact a_left_right,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,
	apply is_measurable_set_prod,
    apply is_measurable.univ,
    trivial,
	apply is_measurable_set_prod,
    apply is_measurable.univ,
	apply is_measurable.univ,
end

@[simp]
lemma is_measurable_6: is_measurable {v: (ℍ × ℕ) × (ℍ × ℕ) | v.snd.snd = 1} :=
begin
    have prod: {v: (ℍ × ℕ) × (ℍ × ℕ) | v.snd.snd = 1} = set.prod (set.prod univ univ) (set.prod univ {n: ℕ | n = 1}), 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
		rw mem_prod_eq,
        split, intro,
        split,
		split,
        rw mem_set_of_eq at *,
        trivial,
		rw mem_set_of_eq at *,
        trivial,
		split,
		rw mem_set_of_eq at *,
        trivial,
		rw mem_set_of_eq at *,
        exact a,
        intro,
        cases a,
		cases a_right,
        rw mem_set_of_eq at *,
        exact a_right_right,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,
	apply is_measurable_set_prod,
    apply is_measurable.univ,
	apply is_measurable.univ,
	apply is_measurable_set_prod,
    apply is_measurable.univ,
	trivial,
end

def male_selected(t: ℍ) := {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.snd = 1 ∧ v.fst.fst = t}

@[simp]
lemma male_selected_is_measurable: ∀ t, is_measurable {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.snd = 1 ∧ v.fst.fst = t} :=
begin
	intros,
	apply is_measurable.inter,
	apply is_measurable_5,
	apply is_measurable_4,
end

def female_selected(t: ℍ) := {v: (ℍ × ℕ) × (ℍ × ℕ) | v.snd.snd = 1 ∧ v.fst.fst = t}

@[simp]
lemma female_selected_is_measurable: ∀ t, is_measurable {v: (ℍ × ℕ) × (ℍ × ℕ) | v.snd.snd = 1 ∧ v.fst.fst = t} :=
begin
	intros,
	apply is_measurable.inter,
	apply is_measurable_6,
	apply is_measurable_4,
end

lemma rw_dive:
	∀ t: ℍ,
	∀ P: ℍ × ℕ → Prop,
	is_measurable (set_of P) → 
	(δ μ) t {v: (ℍ × ℕ) × (ℍ × ℕ) | P v.fst} = (γ μ) t {v: ℍ × ℕ | P v} :=
begin
	intros,
	dunfold δ,
	dunfold γ,
	rw map_apply, simp,
	rw map_apply, simp, 
	unfold code, simp,

	have set_rw: {a: (ℍ × ℕ) × ℍ × ℍ | P a.fst} = set.prod {a: ℍ × ℕ | P a} (set.prod univ univ),
	{
		rw ext_iff,
		intros,
		repeat {rw mem_set_of_eq}, simp,
	},
	rw set_rw, simp, clear set_rw,
	rw prod.prob_measure_apply, simp,
	rw map_apply, simp,

	/- Mundane measurability -/
	simp,
	apply a,
	apply a,
	apply is_measurable.univ,
	simp,
	apply a,
	simp,
	
	/- Interesting example -/
	have prod: {v: (ℍ × ℕ) × (ℍ × ℕ) | P (v.fst)} = set.prod {v: (ℍ × ℕ) | P(v)} univ, 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
        split, intro,
        split,
        rw mem_set_of_eq at *,
        exact a_1,
        rw mem_set_of_eq at *,
        trivial,
        intro,
        cases a_1,
        rw mem_set_of_eq at *,
        exact a_1_left,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,
	exact a,
	apply is_measurable.univ,
end

lemma set_rw_1:
	∀ t: ℍ, 
	set.prod {a: ℍ × ℕ | a.fst = t} (set.prod univ {a: ℍ | generate_binomial_variate_simple(4/5 * t,a) = 1})
	⊆  {a: (ℍ × ℕ) × ℍ × ℍ | (code a).snd.snd = 1 ∧ (code a).fst.fst = t} :=  
begin
	intros,
	unfold set.prod,
	rw set_of_subset_set_of,
	repeat {rw mem_set_of_eq}, simp,

	intros,
	unfold code, simp,

	rw a_1 at *, simp,
	apply generate_binomial_variate_simple_prop_2 b_1.snd (4/5 *t),
	have uni_in:= generate_uniform_variate_simple_in b_1.fst (4/5 * t) 1,
	cases uni_in, assumption,
	assumption,
end

lemma principal:
	∀ t,
	4/5 * t ≤ (δ μ)(t) (female_selected t) :=
begin
	intros,
	unfold female_selected, 

	have foo:= set_rw_1 t,
	have bar:= probability_measure.prob_mono (prod.prob_measure ((γ μ) t) (prod.prob_measure μ μ)) foo,
	clear foo,

	rw prod.prob_measure_apply at bar,
	rw prod.prob_measure_apply at bar,

	have bin_rw:= generate_binomial_variate_simple_prop μ (4/5 * t),
	unfold E_bin at bin_rw,
	rw bin_rw at *, clear bin_rw,

	dunfold δ, 
	rw map_apply, simp,	

	rw test at bar,
	simp at bar,
	exact bar,

	/- Mundane measurability -/
	simp,
	simp,
	apply is_measurable.univ,
	simp,
	simp,
	apply is_measurable_set_prod, 
	apply is_measurable.univ,
	simp,
end

lemma maj:
	∀ t: ℍ, 
	(δ μ)(t) (male_selected t) = t :=
begin
	intros,
	unfold male_selected, 
	
	have rw_1 := rw_dive μ t (λ (v: ℍ × ℕ), v.snd = 1 ∧ v.fst = t),
	rw rw_1, clear rw_1,

	have prop:= maj_ μ t,
	unfold male_selected_ at prop, 
	assumption,
	simp,
end

theorem final:
	∀ t: ℍ,
	(0.8:nnreal) * (δ μ)(t) (male_selected t) ≤ (δ μ)(t) (female_selected t) :=
begin
	intros,
	rw maj,
	apply principal,
end

end relax
