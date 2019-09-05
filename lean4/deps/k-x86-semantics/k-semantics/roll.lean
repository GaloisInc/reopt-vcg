def roll1 : instruction :=
  definst "roll" $ do
    pattern fun cl (v_2663 : reg (bv 32)) => do
      v_4852 <- getRegister rcx;
      v_4854 <- eval (bv_and (extract v_4852 56 64) (expression.bv_nat 8 31));
      v_4855 <- eval (eq v_4854 (expression.bv_nat 8 1));
      v_4856 <- getRegister v_2663;
      v_4858 <- eval (rol v_4856 (concat (expression.bv_nat 24 0) v_4854));
      v_4860 <- eval (isBitSet v_4858 31);
      v_4865 <- eval (eq v_4854 (expression.bv_nat 8 0));
      v_4866 <- eval (notBool_ v_4865);
      v_4868 <- getRegister of;
      v_4875 <- getRegister cf;
      setRegister (lhs.of_reg v_2663) v_4858;
      setRegister cf (bit_or (bit_and v_4866 v_4860) (bit_and v_4865 (eq v_4875 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_4855 (notBool_ (eq (isBitSet v_4858 0) v_4860))) (bit_and (notBool_ v_4855) (bit_or (bit_and v_4866 undef) (bit_and v_4865 (eq v_4868 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2666 : imm int) (v_2668 : reg (bv 32)) => do
      v_4883 <- eval (bv_and (handleImmediateWithSignExtend v_2666 8 8) (expression.bv_nat 8 31));
      v_4884 <- eval (eq v_4883 (expression.bv_nat 8 1));
      v_4885 <- getRegister v_2668;
      v_4887 <- eval (rol v_4885 (concat (expression.bv_nat 24 0) v_4883));
      v_4889 <- eval (isBitSet v_4887 31);
      v_4894 <- eval (eq v_4883 (expression.bv_nat 8 0));
      v_4895 <- eval (notBool_ v_4894);
      v_4897 <- getRegister of;
      v_4904 <- getRegister cf;
      setRegister (lhs.of_reg v_2668) v_4887;
      setRegister cf (bit_or (bit_and v_4895 v_4889) (bit_and v_4894 (eq v_4904 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_4884 (notBool_ (eq (isBitSet v_4887 0) v_4889))) (bit_and (notBool_ v_4884) (bit_or (bit_and v_4895 undef) (bit_and v_4894 (eq v_4897 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2649 : Mem) => do
      v_12291 <- evaluateAddress v_2649;
      v_12292 <- load v_12291 4;
      v_12293 <- getRegister rcx;
      v_12295 <- eval (bv_and (extract v_12293 56 64) (expression.bv_nat 8 31));
      v_12297 <- eval (rol v_12292 (concat (expression.bv_nat 24 0) v_12295));
      store v_12291 v_12297 4;
      v_12299 <- eval (eq v_12295 (expression.bv_nat 8 1));
      v_12301 <- eval (isBitSet v_12297 31);
      v_12306 <- eval (eq v_12295 (expression.bv_nat 8 0));
      v_12307 <- eval (notBool_ v_12306);
      v_12309 <- getRegister of;
      v_12316 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12307 v_12301) (bit_and v_12306 (eq v_12316 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12299 (notBool_ (eq (isBitSet v_12297 0) v_12301))) (bit_and (notBool_ v_12299) (bit_or (bit_and v_12307 undef) (bit_and v_12306 (eq v_12309 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2652 : imm int) (v_2653 : Mem) => do
      v_12322 <- evaluateAddress v_2653;
      v_12323 <- load v_12322 4;
      v_12325 <- eval (bv_and (handleImmediateWithSignExtend v_2652 8 8) (expression.bv_nat 8 31));
      v_12327 <- eval (rol v_12323 (concat (expression.bv_nat 24 0) v_12325));
      store v_12322 v_12327 4;
      v_12329 <- eval (eq v_12325 (expression.bv_nat 8 1));
      v_12331 <- eval (isBitSet v_12327 31);
      v_12336 <- eval (eq v_12325 (expression.bv_nat 8 0));
      v_12337 <- eval (notBool_ v_12336);
      v_12339 <- getRegister of;
      v_12346 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12337 v_12331) (bit_and v_12336 (eq v_12346 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12329 (notBool_ (eq (isBitSet v_12327 0) v_12331))) (bit_and (notBool_ v_12329) (bit_or (bit_and v_12337 undef) (bit_and v_12336 (eq v_12339 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2656 : Mem) => do
      v_14481 <- evaluateAddress v_2656;
      v_14482 <- load v_14481 4;
      v_14483 <- eval (rol v_14482 (expression.bv_nat 32 1));
      store v_14481 v_14483 4;
      v_14486 <- eval (isBitSet v_14483 31);
      setRegister cf v_14486;
      setRegister of (notBool_ (eq (isBitSet v_14483 0) v_14486));
      pure ()
    pat_end
