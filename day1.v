(*Alt + ↓*)
Require Import Arith.

(* 먼저 도구를 확실히 정의합니다 *)
Lemma add_0_r : forall n : nat, n + 0 = n.
Proof. (*induction 수학적 귀납법*)
  induction n as [| n' IHn']. (*Inductive Hypothesis (of) n*)
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. (*rewrite 치환하기 reflexivity 양변이 완벽하게 똑같으니 증명을 끝내라 라는 명령어*)
Qed.

(* 위에서 정의한 도구를 사용합니다 *)
Lemma add_0_0_r : forall n : nat, n + 0 + 0 = n.
Proof.
  intros n.
  rewrite add_0_r.    (* 첫 번째 n+0 처리 *)
  rewrite add_0_r.    (* 두 번째 n+0 처리 *)
  reflexivity.
Qed.