/-
The problem is originally presented in:
A. Pease, G. Sutcliffe, N. Siegel, and S. Trac, “Large Theory
Reasoning with SUMO at CASC,” pp. 1–8, Jul. 2009.
Here we present the natural deduction proof in Lean.
-/

constant U : Type

constants SetOrClass Set Class Object Entity NullList_m List 
          CorpuscularObject Invertebrate Vertebrate Animal SpinalColumn 
          Organism Agent Physical Abstract
          subclass_m TransitiveRelation PartialOrderingRelation : U

constant BananaSlug10 : U

constants exhaustiveDecomposition3 disjointDecomposition3 partition3 : U → U → U → Prop
constant ins : U → U → Prop 
constant subclass : U → U → Prop
constant disjoint : U → U → Prop
constant component : U → U → Prop
constant part : U → U → Prop
constant inList : U → U → Prop
constant ConsFn : U → U → U
constant ListFn1 : U → U
constant ListFn2 : U → U → U
constant ListFn3 : U → U → U → U


/- SUMO axioms -/

variable a72771 : ins Animal SetOrClass
variable a72772 : ins BananaSlug10 Animal
variable a72778 : ins Invertebrate SetOrClass

/- EDITED (see https://github.com/own-pt/cl-krr/issues/23) -/
variable a72773 : ∀ a : U, ((ins a Animal) ∧ (¬ ∃ p : U, ins p SpinalColumn ∧ part p a)) 
  → ¬ ins a Vertebrate

/- EDITED -/
variable a72774 : ¬ ∃ s : U, ins s SpinalColumn ∧ part s BananaSlug10

variable a72761 : ∀ x row0 row1 : U, ins row0 Entity ∧ ins row1 Entity ∧ ins x Entity → 
 ListFn3 x row0 row1 = ConsFn x (ListFn2 row0 row1)

variable a72767 : ∀ x y : U, (ins x Entity ∧ ins y Entity) → 
 (ListFn2 x y) = (ConsFn x (ConsFn y NullList_m))

variable a72768 : ∀ x : U, ins x Entity → (ListFn1 x = ConsFn x NullList_m)

variable a72769 : ∀ x : U, ins x Entity → ¬ inList x NullList_m  

variable a72770 : ∀ L x y : U, (ins x Entity ∧ ins y Entity ∧ ins L List) → 
 (inList x (ConsFn y L)) ↔ ((x = y) ∨ inList x L)

variable a67958 : ins List SetOrClass  
variable a67959 : ins NullList_m List
variable a71402 : ins Vertebrate SetOrClass 
variable a71371 : ins Organism SetOrClass
variable a71872 : ins Agent SetOrClass
variable a71669 : ins Object SetOrClass
variable a69763 : ins Physical SetOrClass
variable a67331 : ins Entity SetOrClass
variable a67448 : ins SetOrClass SetOrClass
variable a68771 : ins Abstract SetOrClass

variable a71370 : partition3 Animal Vertebrate Invertebrate

variable a67131 : ∀ c row0 row1 : U, (ins c Class ∧ ins row0 Class ∧ ins row1 Class) → 
 (partition3 c row0 row1 ↔ (exhaustiveDecomposition3 c row0 row1 ∧ disjointDecomposition3 c row0 row1))

-- EDITED (see https://github.com/own-pt/cl-krr/issues/22)
variable a67115 :
  ∀ (row0 row1 c obj : U),
    ∃ (item : U),
      ins item SetOrClass ∧
        (ins obj Entity →
         ins c SetOrClass ∧ ins c Class ∧
         ins row1 Class ∧ ins row1 Entity ∧ 
         ins row0 Class ∧ ins row0 Entity →
         exhaustiveDecomposition3 c row0 row1 → ins obj c → inList item (ListFn2 row0 row1) ∧ ins obj item)


variable a67447 : partition3 SetOrClass Set Class 
variable a71382 : subclass Vertebrate Animal
variable a71383 : subclass Invertebrate Animal
variable    a15 : ∀ x y z : U, ins x SetOrClass ∧ ins y SetOrClass → (subclass x y ∧ ins z x → ins z y)
variable a67172 : ∃ x : U, ins x Entity
variable a67173 : ∀ c : U, ins c Class ↔ subclass c Entity
variable a71844 : ins TransitiveRelation SetOrClass
variable a72180 : ins PartialOrderingRelation SetOrClass
variable    a13 : ins subclass_m PartialOrderingRelation
variable a67818 : subclass PartialOrderingRelation TransitiveRelation

variable a67809 : ∀ x y z : U, ins x SetOrClass ∧ ins y SetOrClass ∧ ins z SetOrClass → 
  ins subclass_m TransitiveRelation → (subclass x y ∧ subclass y z → subclass x z)

variable a71369 : subclass Animal Organism
variable a71340 : subclass Organism Agent
variable a67315 : subclass Agent Object
variable a67177 : subclass Object Physical
variable a67174 : subclass Physical Entity
variable a67446 : subclass SetOrClass Abstract
variable a67332 : subclass Abstract Entity


-- some initial tests

include a15 a71382 a71383 a71402 a72771
lemma VertebrateAnimal : ∀ (x : U), ins x Vertebrate → ins x Animal := 
begin 
 intros a h,
 have h1, from a15 Vertebrate Animal a,
 apply h1,
 exact (and.intro a71402 a72771),
 exact (and.intro a71382 h)
end
omit a15 a71382 a71383 a71402 a72771

include a15 a71382 a71383 a71402 a72771 a71369 a71371
lemma VertebrateOrganism : ∀ (x : U), ins x Vertebrate → ins x Organism := 
begin 
 intros a h,
 have h1, from a15 Animal Organism a, 
 apply h1,
 exact and.intro a72771 a71371,
 have h2, from (VertebrateAnimal a72771 a71402 a71382 a71383 a15) a h,
 exact and.intro a71369 h2,
end
omit a15 a71382 a71383 a71402 a72771 a71369 a71371

include a15 a72180 a71844 a13 a67818 a71402 a72771 a71371 a71382 a71369 a67809
lemma VertebrateOrganism' : ∀ (x : U), ins x Vertebrate → ins x Organism := 
begin
  intros a h,
  have h₁ : ins subclass_m TransitiveRelation,
    specialize a15 PartialOrderingRelation TransitiveRelation subclass_m,
    apply a15,
    exact ⟨a72180, a71844⟩, 
    exact ⟨a67818, a13⟩, 
  have h₂ : subclass Vertebrate Organism,
    apply a67809 _ Animal _,
    exact ⟨a71402, ⟨a72771, a71371⟩⟩,
    exact h₁,
    exact ⟨a71382, a71369⟩,
  apply a15 Vertebrate _ _,
  exact ⟨a71402, a71371⟩,
  exact ⟨h₂, h⟩
end
omit a15 a72180 a71844 a13 a67818 a71402 a72771 a71371 a71382 a71369 a67809 

include a15 a72180 a71844 a67818 a13
lemma subclass_TransitiveRelation : ins subclass_m TransitiveRelation :=
begin
 specialize a15 PartialOrderingRelation TransitiveRelation subclass_m,
 apply a15,
 exact ⟨ a72180, a71844 ⟩, 
 exact ⟨ a67818, a13 ⟩, 
end
omit a15 a72180 a71844 a67818 a13

include a15 a72180 a71844 a13 a67818 a71402 a72771 a71371 
        a71369 a67809 a71382 a67174 a69763 a67331 a71669 a71340 
        a67315 a67177 a71872
lemma VertebrateEntity : ∀ (x : U), ins x Vertebrate → ins x Entity := 
begin
  intros a h, 
  have h1, from subclass_TransitiveRelation a15 a71844 a72180 a13 a67818,
  have h2 : subclass Vertebrate Organism,
    apply a67809 _ Animal _,
    exact ⟨a71402, ⟨ a72771, a71371 ⟩⟩,
    exact h1,
    exact ⟨a71382, a71369⟩,  
  have h3 : subclass Vertebrate Agent,
    apply a67809 _ Organism _,
    exact ⟨a71402, ⟨ a71371, a71872 ⟩⟩,
    exact h1,
    exact ⟨h2, a71340⟩,
  have h4 : subclass Vertebrate Object,
    apply a67809 _ Agent _,
    exact ⟨a71402, ⟨ a71872, a71669 ⟩⟩,
    exact h1,
    exact ⟨h3, a67315⟩,
  have h5 : subclass Vertebrate Physical,
    apply a67809 _ Object _,
    exact ⟨a71402, ⟨ a71669, a69763 ⟩⟩,
    exact h1,
    exact ⟨h4, a67177⟩,
  have h6 : subclass Vertebrate Entity,
    apply a67809 _ Physical _,
    exact ⟨a71402, ⟨ a69763, a67331 ⟩⟩,
    exact h1,
    exact ⟨ h5, a67174 ⟩,
  apply a15 Vertebrate _ _,
  exact ⟨a71402, a67331⟩,
  exact ⟨h6, h⟩
end
omit a15 a72180 a71844 a13 a67818 a71402 a72771 a71371 
     a71369 a67809 a71382 a67174 a69763 a67331 a71669 a71340 
     a67315 a67177 a71872

-- starting proofs

include a72773 a72774 a72772
lemma l0' (hne : nonempty U) : ¬(ins BananaSlug10 Vertebrate) := by simp *

lemma l0  (hne : nonempty U) : ¬(ins BananaSlug10 Vertebrate) :=
begin
  specialize a72773 BananaSlug10,
  exact a72773 (and.intro a72772 a72774)
end
omit a72773 a72774 a72772


include a67131 a67115
lemma lX  : ∀ x c c1 c2 : U, 
 (ins x Entity ∧ ins c Class ∧ ins c1 Class ∧ ins c2 Class) → 
 (partition3 c c1 c2 ∧ ¬ ins x c1) → ins x c2 := 
begin
 intros a c c1 c2 h1 h2,
 specialize a67131 c c1 c2,
 specialize a67115 c1 c2 c a,
 have h3, from a67131 h1.right,
 have h4, from iff.elim_left h3 h2.left,
 cases a67115 with c2 h5, 
 have h6, from h5.left,
 have h7, from h5.right,
 have h8, from h7 h1.left,
 
end 


include a71369 a67818 a13 a71340 a67315 a67177 a67174 a15 a71844 a72180 a67809 a72771 a71371 a71872 a71669 a69763 a67332

lemma l1 (hne : nonempty U) : subclass Animal Entity :=
begin
  have h, exact ((a15 PartialOrderingRelation TransitiveRelation subclass_m) 
                      (and.intro a72180 a71844)) 
                        (and.intro a67818 a13),
  apply (a67809 Animal Physical Entity),
  simp * at *,
  apply (a67809 Animal Object Physical),
  simp *,
  assumption,
  simp *,
  apply (a67808 Animal Agent Object),
  simp *,
  assumption,
  simp *,  
  apply (a67808 Animal Organism),
  simp *,
  assumption,
  simp *,  
end

include a71402 a71382
lemma l1a (hne : nonempty U) : subclass Vertebrate Entity :=
begin
  have h, exact ((a15 PartialOrderingRelation TransitiveRelation subclass_m) 
                      (and.intro a72202 a71866)) 
                        (and.intro a67817 a13),
  have h₂, from (a67808 Vertebrate Animal Organism) (and.intro a71402 (and.intro a71403 a71390)) h (and.intro a71382 a71388),
  have h₃, from (a67808 Vertebrate Organism Agent) (and.intro a71402 (and.intro a71390 a71894)) h (and.intro h₂ a71359),
  --have h₄, from (a67808 Vertebrate Agent Object) (and.intro a71402 (and.intro a71894 a71691)) h (and.intro h₃ a67315),
  have h₄, from begin apply (a67808 Vertebrate Agent Object), repeat {simp *} end,
  have h₅, from (a67808 Vertebrate Object Physical) (and.intro a71402 (and.intro a71691 a69782)) h (and.intro h₄ a67177),
  have h₆, from (a67808 Vertebrate Physical Entity) (and.intro a71402 (and.intro a69782 a67332)) h (and.intro h₅ a67174),
  exact h₆
end

lemma l1b (hne : nonempty U) : subclass Vertebrate Entity :=
begin
  have h, exact ((a15 PartialOrderingRelation TransitiveRelation subclass_m) 
                      (and.intro a72180 a71844)) (and.intro a67818 a13),
  apply (a67809 Vertebrate Physical Entity),
    exact and.intro a71402 (and.intro a69763 a67332),
    exact h,
    apply and.intro,
      apply (a67808 Vertebrate Object Physical),
        exact and.intro a71402 (and.intro a71691 a69782),
        exact h,
        apply and.intro,
          apply (a67808 Vertebrate Agent Object),
            exact and.intro a71402 (and.intro a71894 a71691),
            exact h,
            apply and.intro,
              apply (a67808 Vertebrate Organism Agent),
                exact and.intro a71402 (and.intro a71390 a71894),
                exact h,
                apply and.intro,
                  apply (a67808 Vertebrate Animal Organism),
                    exact and.intro a71402 (and.intro a71403 a71390),
                    exact h,
                    exact and.intro a71382 a71388,
                  repeat {assumption}
end

lemma l1c (hne : nonempty U) : subclass Vertebrate Entity :=
begin
  have h, exact ((a15 PartialOrderingRelation TransitiveRelation subclass_m) 
                      (and.intro a72180 a71844)) 
                        (and.intro a67818 a13),
  have h1,from begin apply l1, repeat {assumption} end,
  apply a67809 Vertebrate Animal Entity,
  simp *,
  assumption,
  simp *,
  assumption
end

include a67173 
lemma l2  (hne : nonempty U) : ins Vertebrate Class :=
begin
  specialize a67173 Vertebrate,
  rw a67173,
  apply l1b, repeat {assumption}
end

omit a71382 a71402 a67173
include a71383 a72778
lemma l3b (hne : nonempty U) : subclass Invertebrate Entity :=
begin
  have h, exact ((a15 PartialOrderingRelation TransitiveRelation subclass_m) 
                      (and.intro a72202 a71866)) (and.intro a67817 a13),
  apply (a67808 Invertebrate Physical Entity),
    exact and.intro a72778 (and.intro a69782 a67332),
    exact h,
    apply and.intro,
      apply (a67808 Invertebrate Object Physical),
        exact and.intro a72778 (and.intro a71691 a69782),
        exact h,
        apply and.intro,
          apply (a67808 Invertebrate Agent Object),
            exact and.intro a72778 (and.intro a71894 a71691),
            exact h,
            apply and.intro,
              apply (a67808 Invertebrate Organism Agent),
                exact and.intro a72778 (and.intro a71390 a71894),
                exact h,
                apply and.intro,
                  apply (a67808 Invertebrate Animal Organism),
                    exact and.intro a72778 (and.intro a71403 a71390),
                    exact h,
                    simp *,
                  repeat {assumption}
end

include a67173
lemma l4 (hne : nonempty U): ins Invertebrate Class:=
begin
  rw a67173,
  apply l3b, repeat {assumption}
end

--hoping to learn a better way to do this:
omit a67173 a71388 a67817 a13 a71359 a67315 a67177 a67174 a15 a71866 a72202 a67808 a71403 a71390 a71894 a71691 a69782 a67332 a72778 a71383

include a71388 a67817 a13 a71359 a67315 a67177 a67174 a16 a71866 a72202 a67808 a71403 a71390 a71894 a71691 a69782 a67332 a71402 a71382 a67173 a71383 a72778 a67131 a67115 a72772 a71370 a72761 a72767 a72768 a72769 a72770 a67958 a67959 a67446 a67333 a67448 a68791

lemma BS10VI (hne : nonempty U) : ins BananaSlug10 Vertebrate ∨ ins BananaSlug10 Invertebrate :=
begin
  have h₂, exact ((a15 PartialOrderingRelation TransitiveRelation subclass_m) 
                      (and.intro a72202 a71866)) 
                        (and.intro a67817 a13),
  have h₁ : subclass Animal Entity, from begin apply l1, repeat{assumption} end,
  have h₃ : subclass SetOrClass Entity, 
    from
      begin 
        apply (a67808 SetOrClass Abstract Entity), 
        simp *, assumption, simp * 
      end,
  have h : ins Animal Class, from begin rw a67173, exact h₁ end,
  have h₄ : ins Vertebrate Entity, from 
    begin apply (a16 SetOrClass Entity Vertebrate), simp * , simp * end,
  have h₅ : ins Invertebrate Entity, from 
    begin apply (a16 SetOrClass Entity Invertebrate), simp * , simp * end,
  have h1, from begin apply l2, repeat{assumption} end,
  have h2, from begin apply l4, repeat{assumption} end,
  have h3 : exhaustiveDecomposition3 Animal Vertebrate Invertebrate ∧ disjointDecomposition3 Animal Vertebrate Invertebrate, 
    from 
       begin 
         rw ←(a67131 Animal Vertebrate Invertebrate), 
         simp *
       end,
  have h4, from begin exact (a67115 Animal Vertebrate Invertebrate BananaSlug10) end,
  cases h4 with x h4_x,
  have h5 : inList x (ListFn2 Vertebrate Invertebrate) ∧ ins BananaSlug10 x, 
    from 
      begin 
        apply h4_x.right,
        apply (a16 Animal Entity BananaSlug10), simp *,
        simp *,
        simp *,
        exact h3.left,
        assumption
      end,
  have h6 : inList x (ConsFn Vertebrate (ConsFn Invertebrate NullList_m)), from
    begin
      have q : ListFn2 Vertebrate Invertebrate = ConsFn Vertebrate (ConsFn Invertebrate NullList_m), from 
        begin
          apply (a72767 Vertebrate Invertebrate),
          simp *,
        end,
      rw ←q,
      exact h5.left
    end,
  have h7: x = Vertebrate ∨ inList x (ConsFn Invertebrate NullList_m), from
    begin
      rw ←(a72770 (ConsFn Invertebrate NullList_m) x Vertebrate),
      simp * --?
    end,
  cases h7,
    rw ←h7,
    exact or.inl h5.right,
    have h8 : x = Invertebrate ∨ inList x NullList_m, from
      begin
        rw ←(a72770 NullList_m x Invertebrate), 
        simp *
      end,
    cases h8,
      rw ←h8,
      exact or.inr h5.right,
      apply false.elim,
        apply a72769 x,
          apply a16 SetOrClass Entity x,
            simp *, simp *,
        assumption
end

include a72773 a72774
theorem goal (hne: nonempty U) : ins BananaSlug10 Invertebrate :=
begin
  have h, from begin apply BS10VI, repeat{assumption} end,
  cases h,
  apply false.elim,
    apply l0, 
   repeat{assumption}
end

-- tem como provar?
variable axiom4 : ¬ (Vertebrate = Invertebrate) 
