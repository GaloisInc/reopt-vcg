def insertps1 : instruction :=
  definst "insertps" $ do
    pattern fun (v_3098 : imm int) (v_3099 : reg (bv 128)) (v_3100 : reg (bv 128)) => do
      v_5326 <- eval (handleImmediateWithSignExtend v_3098 8 8);
      v_5328 <- eval (extract v_5326 2 4);
      v_5329 <- eval (eq v_5328 (expression.bv_nat 2 0));
      v_5330 <- getRegister v_3100;
      v_5331 <- eval (extract v_5330 0 32);
      v_5332 <- eval (eq v_5328 (expression.bv_nat 2 1));
      v_5333 <- eval (eq v_5328 (expression.bv_nat 2 2));
      v_5334 <- eval (extract v_5326 0 2);
      v_5336 <- getRegister v_3099;
      v_5345 <- eval (mux (eq v_5334 (expression.bv_nat 2 0)) (extract v_5336 96 128) (mux (eq v_5334 (expression.bv_nat 2 1)) (extract v_5336 64 96) (mux (eq v_5334 (expression.bv_nat 2 2)) (extract v_5336 32 64) (extract v_5336 0 32))));
      v_5351 <- eval (extract v_5330 32 64);
      v_5358 <- eval (extract v_5330 64 96);
      setRegister (lhs.of_reg v_3100) (concat (concat (concat (mux (isBitSet v_5326 4) (expression.bv_nat 32 0) (mux v_5329 v_5331 (mux v_5332 v_5331 (mux v_5333 v_5331 v_5345)))) (mux (isBitSet v_5326 5) (expression.bv_nat 32 0) (mux v_5329 v_5351 (mux v_5332 v_5351 (mux v_5333 v_5345 v_5351))))) (mux (isBitSet v_5326 6) (expression.bv_nat 32 0) (mux v_5329 v_5358 (mux v_5332 v_5345 v_5358)))) (mux (isBitSet v_5326 7) (expression.bv_nat 32 0) (mux v_5329 v_5345 (extract v_5330 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3093 : imm int) (v_3094 : Mem) (v_3095 : reg (bv 128)) => do
      v_8614 <- eval (handleImmediateWithSignExtend v_3093 8 8);
      v_8616 <- eval (extract v_8614 2 4);
      v_8617 <- eval (eq v_8616 (expression.bv_nat 2 0));
      v_8618 <- getRegister v_3095;
      v_8619 <- eval (extract v_8618 0 32);
      v_8620 <- eval (eq v_8616 (expression.bv_nat 2 1));
      v_8621 <- eval (eq v_8616 (expression.bv_nat 2 2));
      v_8622 <- evaluateAddress v_3094;
      v_8623 <- load v_8622 4;
      v_8629 <- eval (extract v_8618 32 64);
      v_8636 <- eval (extract v_8618 64 96);
      setRegister (lhs.of_reg v_3095) (concat (concat (concat (mux (isBitSet v_8614 4) (expression.bv_nat 32 0) (mux v_8617 v_8619 (mux v_8620 v_8619 (mux v_8621 v_8619 v_8623)))) (mux (isBitSet v_8614 5) (expression.bv_nat 32 0) (mux v_8617 v_8629 (mux v_8620 v_8629 (mux v_8621 v_8623 v_8629))))) (mux (isBitSet v_8614 6) (expression.bv_nat 32 0) (mux v_8617 v_8636 (mux v_8620 v_8623 v_8636)))) (mux (isBitSet v_8614 7) (expression.bv_nat 32 0) (mux v_8617 v_8623 (extract v_8618 96 128))));
      pure ()
    pat_end
