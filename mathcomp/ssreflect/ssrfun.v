From mathcomp Require Import ssreflect.
From HoTT Require Export ssrfun.
From mathcomp Require Export ssrnotations.

Lemma Some_inj {T : nonPropType} : injective (@Some T).
Proof. by move=> x y []. Qed.
