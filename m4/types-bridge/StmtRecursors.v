(* §AR-m4-routes.reporting.bridge: Check the actual exported recursive representations. *)
From LeanImport Require Import Lean.
Require Import TypePrefix StmtPrefix.
Set Universe Polymorphism.
Section Recursors_type.
Universe result.

Variables (P : CC_Stmt -> Type@{result}) (Q : CC_LStmts -> Type@{result}).
Variable fskip : P CC_Stmt_Sskip.
Variable fassign : forall e1 e2, P(CC_Stmt_Sassign e1 e2).
Variable fset : forall id e, P(CC_Stmt_Sset id e).
Variable fcall : forall id e el, P(CC_Stmt_Scall id e el).
Variable fbuiltin : forall id ef tyl el, P(CC_Stmt_Sbuiltin id ef tyl el).
Variable fsequence : forall s1 s2, P s1 -> P s2 -> P(CC_Stmt_Ssequence s1 s2).
Variable fif : forall e s1 s2, P s1 -> P s2 -> P(CC_Stmt_Sifthenelse e s1 s2).
Variable floop : forall s1 s2, P s1 -> P s2 -> P(CC_Stmt_Sloop s1 s2).
Variable fbreak : P CC_Stmt_Sbreak.
Variable fcontinue : P CC_Stmt_Scontinue.
Variable freturn : forall e, P(CC_Stmt_Sreturn e).
Variable fswitch : forall e ls, Q ls -> P(CC_Stmt_Sswitch e ls).
Variable flabel : forall id s, P s -> P(CC_Stmt_Slabel id s).
Variable fgoto : forall id, P(CC_Stmt_Sgoto id).
Variable fnil : Q CC_LStmts_LSnil.
Variable fcons : forall id s ls, P s -> Q ls -> Q(CC_LStmts_LScons id s ls).
Fixpoint cc_stmt_type(s:CC_Stmt) {struct s} : P s :=
 match s as s0 return P s0 with
 | CC_Stmt_Sskip => fskip
 | CC_Stmt_Sassign e1 e2 => fassign e1 e2
 | CC_Stmt_Sset id e => fset id e
 | CC_Stmt_Scall id e el => fcall id e el
 | CC_Stmt_Sbuiltin id ef tyl el => fbuiltin id ef tyl el
 | CC_Stmt_Ssequence s1 s2 => fsequence s1 s2 (cc_stmt_type s1)(cc_stmt_type s2)
 | CC_Stmt_Sifthenelse e s1 s2 => fif e s1 s2 (cc_stmt_type s1)(cc_stmt_type s2)
 | CC_Stmt_Sloop s1 s2 => floop s1 s2 (cc_stmt_type s1)(cc_stmt_type s2)
 | CC_Stmt_Sbreak => fbreak
 | CC_Stmt_Scontinue => fcontinue
 | CC_Stmt_Sreturn e => freturn e
 | CC_Stmt_Sswitch e ls => fswitch e ls (cc_lstmts_type ls)
 | CC_Stmt_Slabel id s => flabel id s (cc_stmt_type s)
 | CC_Stmt_Sgoto id => fgoto id
 end
with cc_lstmts_type(ls:CC_LStmts) {struct ls} : Q ls :=
 match ls as ls0 return Q ls0 with
 | CC_LStmts_LSnil => fnil
 | CC_LStmts_LScons id s tail => fcons id s tail (cc_stmt_type s)(cc_lstmts_type tail)
 end.
End Recursors_type.
Print Assumptions cc_stmt_type.
Print Assumptions cc_lstmts_type.
Section Recursors_sprop.

Variables (P : CC_Stmt -> SProp) (Q : CC_LStmts -> SProp).
Variable fskip : P CC_Stmt_Sskip.
Variable fassign : forall e1 e2, P(CC_Stmt_Sassign e1 e2).
Variable fset : forall id e, P(CC_Stmt_Sset id e).
Variable fcall : forall id e el, P(CC_Stmt_Scall id e el).
Variable fbuiltin : forall id ef tyl el, P(CC_Stmt_Sbuiltin id ef tyl el).
Variable fsequence : forall s1 s2, P s1 -> P s2 -> P(CC_Stmt_Ssequence s1 s2).
Variable fif : forall e s1 s2, P s1 -> P s2 -> P(CC_Stmt_Sifthenelse e s1 s2).
Variable floop : forall s1 s2, P s1 -> P s2 -> P(CC_Stmt_Sloop s1 s2).
Variable fbreak : P CC_Stmt_Sbreak.
Variable fcontinue : P CC_Stmt_Scontinue.
Variable freturn : forall e, P(CC_Stmt_Sreturn e).
Variable fswitch : forall e ls, Q ls -> P(CC_Stmt_Sswitch e ls).
Variable flabel : forall id s, P s -> P(CC_Stmt_Slabel id s).
Variable fgoto : forall id, P(CC_Stmt_Sgoto id).
Variable fnil : Q CC_LStmts_LSnil.
Variable fcons : forall id s ls, P s -> Q ls -> Q(CC_LStmts_LScons id s ls).
Fixpoint cc_stmt_sprop(s:CC_Stmt) {struct s} : P s :=
 match s as s0 return P s0 with
 | CC_Stmt_Sskip => fskip
 | CC_Stmt_Sassign e1 e2 => fassign e1 e2
 | CC_Stmt_Sset id e => fset id e
 | CC_Stmt_Scall id e el => fcall id e el
 | CC_Stmt_Sbuiltin id ef tyl el => fbuiltin id ef tyl el
 | CC_Stmt_Ssequence s1 s2 => fsequence s1 s2 (cc_stmt_sprop s1)(cc_stmt_sprop s2)
 | CC_Stmt_Sifthenelse e s1 s2 => fif e s1 s2 (cc_stmt_sprop s1)(cc_stmt_sprop s2)
 | CC_Stmt_Sloop s1 s2 => floop s1 s2 (cc_stmt_sprop s1)(cc_stmt_sprop s2)
 | CC_Stmt_Sbreak => fbreak
 | CC_Stmt_Scontinue => fcontinue
 | CC_Stmt_Sreturn e => freturn e
 | CC_Stmt_Sswitch e ls => fswitch e ls (cc_lstmts_sprop ls)
 | CC_Stmt_Slabel id s => flabel id s (cc_stmt_sprop s)
 | CC_Stmt_Sgoto id => fgoto id
 end
with cc_lstmts_sprop(ls:CC_LStmts) {struct ls} : Q ls :=
 match ls as ls0 return Q ls0 with
 | CC_LStmts_LSnil => fnil
 | CC_LStmts_LScons id s tail => fcons id s tail (cc_stmt_sprop s)(cc_lstmts_sprop tail)
 end.
End Recursors_sprop.
Print Assumptions cc_stmt_sprop.
Print Assumptions cc_lstmts_sprop.
