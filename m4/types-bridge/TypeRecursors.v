(* §AR-m4-routes.reporting.bridge: Check the actual exported recursive representations. *)
From LeanImport Require Import Lean.
Require Import TypePrefix.
Set Universe Polymorphism.
Section Recursors_type.
Universe result.

Variables (P : CC_Ty -> Type@{result}) (Q : List_inst1 CC_Ty -> Type@{result}).
Variable fv : P CC_Ty_Tvoid.
Variable fi : forall sz sg a, P(CC_Ty_Tint sz sg a).
Variable fl : forall sg a, P(CC_Ty_Tlong sg a).
Variable ff : forall sz a, P(CC_Ty_Tfloat sz a).
Variable fp : forall t a, P t -> P(CC_Ty_Tpointer t a).
Variable fa : forall t sz a, P t -> P(CC_Ty_Tarray t sz a).
Variable ffun : forall xs ret cc, Q xs -> P ret -> P(CC_Ty_Tfunction xs ret cc).
Variable fs : forall id a, P(CC_Ty_Tstruct id a).
Variable fu : forall id a, P(CC_Ty_Tunion id a).
Variable fnil : Q(List_nil_inst1 CC_Ty).
Variable fcons : forall head tail, P head -> Q tail -> Q(List_cons_inst1 CC_Ty head tail).
Fixpoint cc_ty_type(t:CC_Ty) {struct t} : P t :=
 match t as t0 return P t0 with
 | CC_Ty_Tvoid => fv
 | CC_Ty_Tint sz sg a => fi sz sg a
 | CC_Ty_Tlong sg a => fl sg a
 | CC_Ty_Tfloat sz a => ff sz a
 | CC_Ty_Tpointer child a => fp child a (cc_ty_type child)
 | CC_Ty_Tarray child sz a => fa child sz a (cc_ty_type child)
 | CC_Ty_Tfunction xs ret cc =>
    let fix nested(xs:List_inst1 CC_Ty) : Q xs :=
     match xs as xs0 return Q xs0 with
     | List_nil_inst1 _ => fnil
     | List_cons_inst1 _ head tail => fcons head tail (cc_ty_type head)(nested tail)
     end in
    ffun xs ret cc (nested xs)(cc_ty_type ret)
 | CC_Ty_Tstruct id a => fs id a
 | CC_Ty_Tunion id a => fu id a
 end.
Fixpoint cc_ty_list_type(xs:List_inst1 CC_Ty) : Q xs :=
 match xs as xs0 return Q xs0 with
 | List_nil_inst1 _ => fnil
 | List_cons_inst1 _ head tail => fcons head tail (cc_ty_type head)(cc_ty_list_type tail)
 end.
End Recursors_type.
Print Assumptions cc_ty_type.
Print Assumptions cc_ty_list_type.
Section Recursors_sprop.

Variables (P : CC_Ty -> SProp) (Q : List_inst1 CC_Ty -> SProp).
Variable fv : P CC_Ty_Tvoid.
Variable fi : forall sz sg a, P(CC_Ty_Tint sz sg a).
Variable fl : forall sg a, P(CC_Ty_Tlong sg a).
Variable ff : forall sz a, P(CC_Ty_Tfloat sz a).
Variable fp : forall t a, P t -> P(CC_Ty_Tpointer t a).
Variable fa : forall t sz a, P t -> P(CC_Ty_Tarray t sz a).
Variable ffun : forall xs ret cc, Q xs -> P ret -> P(CC_Ty_Tfunction xs ret cc).
Variable fs : forall id a, P(CC_Ty_Tstruct id a).
Variable fu : forall id a, P(CC_Ty_Tunion id a).
Variable fnil : Q(List_nil_inst1 CC_Ty).
Variable fcons : forall head tail, P head -> Q tail -> Q(List_cons_inst1 CC_Ty head tail).
Fixpoint cc_ty_sprop(t:CC_Ty) {struct t} : P t :=
 match t as t0 return P t0 with
 | CC_Ty_Tvoid => fv
 | CC_Ty_Tint sz sg a => fi sz sg a
 | CC_Ty_Tlong sg a => fl sg a
 | CC_Ty_Tfloat sz a => ff sz a
 | CC_Ty_Tpointer child a => fp child a (cc_ty_sprop child)
 | CC_Ty_Tarray child sz a => fa child sz a (cc_ty_sprop child)
 | CC_Ty_Tfunction xs ret cc =>
    let fix nested(xs:List_inst1 CC_Ty) : Q xs :=
     match xs as xs0 return Q xs0 with
     | List_nil_inst1 _ => fnil
     | List_cons_inst1 _ head tail => fcons head tail (cc_ty_sprop head)(nested tail)
     end in
    ffun xs ret cc (nested xs)(cc_ty_sprop ret)
 | CC_Ty_Tstruct id a => fs id a
 | CC_Ty_Tunion id a => fu id a
 end.
Fixpoint cc_ty_list_sprop(xs:List_inst1 CC_Ty) : Q xs :=
 match xs as xs0 return Q xs0 with
 | List_nil_inst1 _ => fnil
 | List_cons_inst1 _ head tail => fcons head tail (cc_ty_sprop head)(cc_ty_list_sprop tail)
 end.
End Recursors_sprop.
Print Assumptions cc_ty_sprop.
Print Assumptions cc_ty_list_sprop.
