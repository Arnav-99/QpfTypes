import Qpf
import Qpf.Examples._01_List
import Qpf.Macro.Tactic.FinDestr
import Qpf.MathlibPort.Fin2
-- import Qpf.Qpf.Multivariate.Constructions.Comp

open MvQPF

/-
  # Rose trees
  Now let us look at Rose Trees, that is, trees where each node has a label of type `α` and an arbitrary
  number of children.

  ```lean4
  inductive QpfTree (α : Type)
  | node : α → QpfList (QpfTree α) → QpfTree α
  ```

  First, we extract the shape functor. That is, we replace each distinct expression (which is not
  already a type variable) with a new type variable.
  In this case, that is only `QpfList (QpfTree α)`, which we represent with `β`

  ```lean4
  inductive QpfTree.Shape (α β : Type)
  | node : α → β  → QpfTree.Shape α β γ
  ```
-/


namespace QpfTree
  namespace Shape
    /-
      Since there is only one constructor, `def HeadT := Unit` would also have sufficed
    -/
    inductive HeadT
      -- | leaf
      | node

    abbrev ChildT : HeadT → TypeVec 2
      -- | .leaf => ![PFin2 1, PFin2 0, PFin2 0, PFin2 0]
      | .node => ![PFin2 1, PFin2 1]
      --| .node, _ => Unit

    abbrev P := MvPFunctor.mk HeadT ChildT

    -- abbrev F := P.Obj.curried
    abbrev F := TypeFun.curried P.Obj

    instance : MvFunctor P.Obj := by infer_instance
  end Shape

  /-
    Before we can take the fixpoint, we need to compose this shape functor with QpfList in the second
    argument. Effectively, we want to define
    ```
      F α β := Shape.F α (QpfList β)
    ```

    Note that we don't care too much about whether `F` is a polynomial functor, we just require it
    to be a QPF, so we'll invoke the composition of QPFs here.

    To do so, we have to supply two binary functors to be composed with `Shape.P.Obj`.
    The first functor is trivial, it's the projection to the second argument (we count the
    arguments right-to-left, since that is how the `Vec`s are built).
    ```
      G₁ α β := α           -- (hence, G₁ := Prj 1)
    ```
    The second functor is a bit more involved. We want to invoke `QpfList`, which expects a single
    argument, but `G₂` should be a binary functor. Additionally, the argument we want to apply
    `QpfList` to is `β`, the second argument, so we compose `QpfList` with a projection functor
    ```
      G₂ α β := QpfList β   -- (hence, G₂ := Comp QpfList' ![Prj 0])
    ```
  -/

  #check Fin2
  #check Fix.mk

  abbrev G' (j : Fin2 1) : TypeVec 2 → Type := Prj 0

  abbrev G (i : Fin2 2) : TypeVec 2 → Type :=
    match i with
    | 0 => Comp QpfList' G'
    | 1 => Prj 1


  /-
  def G : Fin2 2 → TypeVec 2 -> Type := !![
        Prj 1,
        --Comp QpfList' !![@Prj 2 0]
        Comp QpfList' ![@Prj 2 0]
    ]
  -/

  #check ![@Prj 2 0]
  #check !![@Prj 2 0]

  abbrev Base : TypeFun 2
    := Comp Shape.P.Obj G

  def F' := Shape.P.Obj

  instance : MvFunctor Shape.P.Obj := by infer_instance
  instance : MvQPF Shape.P.Obj := by infer_instance

  instance (i : Fin2 2) : MvFunctor (G i) := by
    match i with
    | .fz => simp [G]; infer_instance
    | .fs s =>
      simp [G]
      split
      · contradiction      -- Alternatively, rename _ => h; revert h; exact Fin2.elim0
      · infer_instance

  instance : MvFunctor Base := by infer_instance

  -- CC: This is having trouble type-checking?
  --instance : MvQPF (fun (i : Fin2 1) =>
  --    Matrix.vecCons (Prj 1) ![] (Fin.rev (PFin2.toFin (PFin2.ofFin2 i)))) := by

  --  done\

  #check Comp

  instance (i : Fin2 2) : MvQPF (G i) := by
    match i with
    | .fz => simp [G]; infer_instance
    | .fs s =>
      simp [G]
      match s with
      | .fz =>
        simp
        infer_instance
        done
      | .fs s' => revert s'; exact Fin2.elim0

  instance : MvQPF Base := by infer_instance

  abbrev QpfTree' := Fix Base
  abbrev QpfTree  := TypeFun.curried QpfTree'

  #check @Prj 2 1
  #check Shape.F
  #check Shape.P.Obj
  #check Vec.append1

  #check ![@Prj 2 0]
  #check !![@Prj 2 0]

  instance : MvFunctor QpfList' := by infer_instance


  /-
    There is also a `qpf` command, which will define the right projections and compositions for us!
  -/
  qpf F_curried α β := Shape.F α (QpfList β)

  --abbrev F := F_curried.typefun

    -- -- Unfold the definitions, to see both are applications of `Comp`
    -- dsimp [F_manual, F_curried.typefun]
    -- apply congrArg;

    -- -- At this point, the goal is to show that two vectors, of known size are equal.
    -- -- These vectors are not definitially equal, but their respective elements are.
    -- funext i;
    -- -- The following tactic takes a `i : Fin2 n`, where `n` is a known constant, and breaks the goal
    -- -- into `n` subgoals, one for each concrete possible value of `i`
    -- fin_destr i <;> rfl



  /-
    Type class inference works as expected, it can reason about the vectors of functors involved
    in compositions
  -/
  --example : MvQPF F := by infer_instance

  --abbrev QpfTree' := Fix F
  --abbrev QpfTree  := QpfTree'.curried

  /-
    The command will give us a curried type function, the internal, uncurried, function can be found
    under `.typefun`
  -/
  -- #check (F_curried : Type _ → Type _ → Type _)
  -- #check (F_curried.typefun : TypeFun 2)

  -- abbrev F := F_curried.typefun

    -- -- Unfold the definitions, to see both are applications of `Comp`
    -- dsimp [F_manual, F_curried.typefun]
    -- apply congrArg;

    -- -- At this point, the goal is to show that two vectors, of known size are equal.
    -- -- These vectors are not definitially equal, but their respective elements are.
    -- funext i;
    -- -- The following tactic takes a `i : Fin2 n`, where `n` is a known constant, and breaks the goal
    -- -- into `n` subgoals, one for each concrete possible value of `i`
    -- fin_destr i <;> rfl



  /-
    Type class inference works as expected, it can reason about the vectors of functors involved
    in compositions
  -/

  -- example : MvQPF  := by infer_instance

  set_option trace.Meta.synthInstance true
  set_option trace.profiler true

  -- instance : MvQPF (Comp F' G : TypeFun 2) where
  --   P := sorry
  --   abs := sorry
  --   repr {α} := sorry
  --   abs_repr := sorry
  --   abs_map := sorry

  -- instance : MvFunctor Base where map := sorry

  -- example : MvQPF Base := by infer_instance

  /-
  abbrev Base : TypeFun 2
    := Comp Shape.P.Obj G

      nm: ℕ
      F: TypeVec.{u} n → Type u_1
      fF: MvFunctor F
      q: MvQPF F
      G: Fin2 n → TypeVec.{u} m → Type u
      fG: (i : Fin2 n) → MvFunctor (G i)
      q': (i : Fin2 n) → MvQPF (G i)
      αβ: TypeVec.{u} m
      f: α ⟹ β
      ⊢ MvPFunctor.{u} m

  instance : MvQPF (Comp F G) where
  P := MvPFunctor.comp (P F) fun i ↦ P <| G i
  abs := Comp.mk ∘ (map fun i ↦ abs) ∘ abs ∘ MvPFunctor.comp.get
  repr {α} := MvPFunctor.comp.mk ∘ repr ∘
              (map fun i ↦ (repr : G i α → (fun i : Fin2 n ↦ Obj (P (G i)) α) i)) ∘ Comp.get
  abs_repr := by
    intros
    simp (config := { unfoldPartialApp := true }) only [Function.comp_def, comp.get_mk, abs_repr,
      map_map, TypeVec.comp, MvFunctor.id_map', Comp.mk_get]
  abs_map := by
    intros
    simp only [(· ∘ ·)]
    rw [← abs_map]
    simp (config := { unfoldPartialApp := true }) only [comp.get_map, map_map, TypeVec.comp,
      abs_map, map_mk]
  -/

  --instance : MvQPF (Comp Shape.P.Obj G) := by infer_instance

  -- instance : MvQPF Base where
  --   P := MvPFunctor.comp (P Shape.P.Obj) fun i ↦ P <| G i
  --   abs := sorry
  --   repr {α} := sorry
  --   abs_repr := sorry
  --   abs_map := sorry

  --abbrev QpfTree' := Fix Base
  --abbrev QpfTree  := TypeFun.curried QpfTree'

  namespace debug

  variable (α)
  #check (Comp (QpfList') (!![@Prj 2 0]))
  end debug

  /-
  ## Constructor

  -- We'd like to take `QpfList (QpfTree α)` as an argument, since that is what users expect.
  -- However, `Fix.mk` expects something akin to `(Comp QpfList' ![Prj 0]) ![_, QpfTree' ![α]]`,
  -- which is not definitionally equal, so we'll have to massage the types a bit
  -/

  -- namespace debug

  -- variable (α)

  -- def oops := (fun (i : Fin2 4) =>
  --     (fun i => G (Fin.rev (PFin2.toFin (PFin2.ofFin2 i)))) i
  --       (Vec.reverse (Vec.append1 Vec.nil α) ::: Fix Base (Vec.reverse (Vec.append1 Vec.nil α)))) 0

  -- end debug

  def node (a : α) (children : QpfList (QpfTree α)) : QpfTree α :=
    Fix.mk ⟨Shape.HeadT.node,
            fun i _ => match i with
            | 0 => by
                    apply cast ?_ children;
                    unfold QpfList;
                    dsimp only [TypeFun.curried, TypeFun.curriedAux, TypeFun.reverseArgs];
                    apply congrArg;
                    vec_eq;
            | .fs .fz => a
    ⟩

  /-
    Even though there are some `sorry`s left in the formalization codebase, all of the machinery
    for inductive types is fully proven, and indeed, we can construct `QpfTree` without depending
    on `sorryAx`
  -/
  #print axioms node

  #check TypeVec.Arrow

  #check TypeFun

  #check Comp
  #check Vec.reverse_involution

  #check PFin2
  #check Vec

  theorem curried_uncurried_equal (β : Type)
  -- (f : TypeVec.Arrow (Shape.ChildT Shape.HeadT.node) fun i =>
  -- G i ((Vec.reverse (Vec.append1 Vec.nil β)) ::: (Fix Base (Vec.reverse (Vec.append1 Vec.nil β)))))
  : QpfList' (fun (i : Fin2 1) => QpfTree β) = QpfList (QpfTree β) := by
  {
    suffices ts : (TypeFun.curriedAux (QpfList')) (QpfTree β) = QpfList' (fun (i : Fin2 1) => QpfTree β)
    suffices ts2 : ∀ v : TypeVec 1, (TypeFun.reverseArgs QpfList') v = QpfList' v
    let ts3 : TypeFun.reverseArgs QpfList' = QpfList':= funext ts2
    let ts4 : QpfList' (fun (i : Fin2 1) => QpfTree β) = QpfList (QpfTree β) := by {
      let rw1 : QpfList = TypeFun.curried (QpfList') := by trivial
      rw [rw1]
      rw [TypeFun.curried, ts3, ts]
    };
    trivial

    intro v
    rw [TypeFun.reverseArgs]
    apply congrArg
    let test2 : ∀ j : Fin2 1, (Vec.reverse v) j = v j := by {
      intro j
      conv =>
        lhs
        simp [Vec.reverse, Fin2.inv]
      apply congrArg
      cases (PFin2.ofFin2 j)
      let test3 : @PFin2.inv 1 (PFin2.fz) = PFin2.fz := by trivial
      rw [test3]
      rw [← (@PFin2.ofFin2_toFin2_iso 1 j)]
      apply congrArg
      cases (PFin2.ofFin2 j)
      trivial
      contradiction
      contradiction
    };
    exact funext test2

    conv =>
        lhs
        rw [TypeFun.curriedAux]
        simp

    -- apply congrArg
    -- let test1 : ∀ i : Fin2 1, (Vec.append1 Vec.nil (QpfTree β)) i = (fun i => QpfTree β) i := by {
    --   intro i
    --   conv =>
    --     rhs
    --     simp
    --   conv =>
    --     lhs
    --     simp [Vec.append1]
    --   split
    --   contradiction
    --   trivial
    -- }
    -- exact (funext test1)
  }

  def rec {β}
          {motive : QpfTree β → Sort}
          : ((elem : β)
          → (children : QpfList (QpfTree β))
          → (motive (node elem children)))
          → (t : QpfTree β)
          → (motive t) :=
  fun given_hyp t => by {
    let t' := Fix.dest t;
    rcases t' with ⟨a, f⟩;

    -- type signature for f post simp mysteriously changed
    cases a ; simp [MvPFunctor.B] at f;
    let required_equality := curried_uncurried_equal β

    -- repair work for mysterious type change
    let type_equality : (fun i => G i ((Vec.reverse fun i => β) ::: Fix Base (Vec.reverse fun i => β))) 0 = QpfList' (fun (i : Fin2 1) => QpfTree β) := by {
      sorry
    }

    let children := f 0 .fz
    rw [type_equality] at children
    rw [required_equality] at children
    let elem : β := f 1 .fz

    let ts5 := given_hyp elem children

    suffices final_equality : (node elem children) = t
    rw [final_equality] at ts5
    trivial

    -- extremely weird, this was not an issue before!

    -- let type_equality2 : Matrix.vecCons β ![] (Fin.rev (PFin2.toFin (PFin2.ofFin2 i))) = β := by sorry
    suffices fix_expansion_equality : Fix.mk ⟨Shape.HeadT.node, f⟩ = t

    let ⟨Shape.HeadT.node, f_left⟩ := Fix.dest (node elem children)
    -- si
    -- apply congrArg
    -- apply congrArg

    -- let t' : ∀ v : TypeVec 2, (G 0) v = QpfList' !![v 0] := by {
    --   intro v;
    --   let t1 : G 0 = Comp QpfList' !![@Prj 2 0] := by trivial;
    --   rw [t1];
    --   simp [Comp];
    --   apply congrArg;
    --   sorry;
    -- };
    -- rw [t'] at children';
    -- suffices children_converted : QpfList (QpfTree β);
    -- let ind_res := given_hyp (f 1 .fz) (children_converted);
    -- suffices h : node (f 1 .fz) (children_converted) = t;
    -- rw [h] at ind_res;
    -- trivial;
    -- sorry;
    -- sorry;
  }

end QpfTree

#check funext



export QpfTree (QpfTree QpfTree')
