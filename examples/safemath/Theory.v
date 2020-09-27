Require Import SafeMath.SafeMath.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* trivial observation that there is only one possible state *)
Lemma state_constant : forall s, s = state.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.


Theorem mul_correct : forall s y x, reachable s ->
  range256 x /\ range256 y /\ range256 (x * y) <-> mul_ret s y x = Some (x * y).

Proof.
  intros.
  split. {

    intros.
    destruct H0 as [Hx [Hy Hxy]].
    rewrite (state_constant s).
    unfold mul_ret. simpl.

    assert (0 <=? x * y = true) as assertion. {
      apply (proj2 (Z.leb_le 0 (x * y))).
      destruct Hxy. assumption.
    }
    rewrite assertion. clear assertion.

    assert (x * y <=? UINT_MAX 256 = true) as assertion. {
      apply (proj2 (Z.leb_le (x * y) (UINT_MAX 256))).
      destruct Hxy. assumption.
    }
    rewrite assertion. clear assertion.

    assert (0 <=? y = true) as assertion. {
      apply (proj2 (Z.leb_le 0 y)).
      destruct Hy. assumption.
    }
    rewrite assertion. clear assertion.

    assert (y <=? UINT_MAX 256 = true) as assertion. {
      apply (proj2 (Z.leb_le y (UINT_MAX 256))).
      destruct Hy. assumption.
    }
    rewrite assertion. clear assertion.

    assert (0 <=? x = true) as assertion. {
      apply (proj2 (Z.leb_le 0 x)).
      destruct Hx. assumption.
    }
    rewrite assertion. clear assertion.

    assert (x <=? UINT_MAX 256 = true) as assertion. {
      apply (proj2 (Z.leb_le x (UINT_MAX 256))).
      destruct Hx. assumption.
    }
    rewrite assertion. clear assertion.

    simpl.
    assert ((x * y) mod (MOD 256) = x * y) as Hmod.
    apply range_mod. assumption.
    rewrite Hmod. reflexivity.

  } {

    intros.
    unfold mul_ret in H0.
    simpl in H0.
    apply ite_true in H0.
    apply andb_prop in H0.
    destruct H0.
    apply andb_prop in H0.
    destruct H0.
    apply andb_prop in H1.
    destruct H1.
    apply andb_prop in H1.
    destruct H1.
    apply andb_prop in H3.
    destruct H3.
    apply andb_prop in H3.
    destruct H3.
    clear H5.
    split. split.
    apply Zle_bool_imp_le. assumption.
    apply Zle_bool_imp_le. assumption.
    split. split.
    apply Zle_bool_imp_le. assumption.
    apply Zle_bool_imp_le. assumption.
    split.
    apply Zle_bool_imp_le. assumption.
    apply Zle_bool_imp_le. assumption.
    unfold not. intros. discriminate.

  }
Qed. Check mul_correct.
