def insertps1 : instruction :=
  definst "insertps" $ do
    pattern fun (v_3071 : imm int) (v_3073 : reg (bv 128)) (v_3074 : reg (bv 128)) => do
      v_5310 <- eval (handleImmediateWithSignExtend v_3071 8 8);
      v_5312 <- eval (extract v_5310 2 4);
      v_5313 <- eval (eq v_5312 (expression.bv_nat 2 0));
      v_5314 <- getRegister v_3074;
      v_5315 <- eval (extract v_5314 0 32);
      v_5316 <- eval (eq v_5312 (expression.bv_nat 2 1));
      v_5317 <- eval (eq v_5312 (expression.bv_nat 2 2));
      v_5318 <- eval (extract v_5310 0 2);
      v_5320 <- getRegister v_3073;
      v_5329 <- eval (mux (eq v_5318 (expression.bv_nat 2 0)) (extract v_5320 96 128) (mux (eq v_5318 (expression.bv_nat 2 1)) (extract v_5320 64 96) (mux (eq v_5318 (expression.bv_nat 2 2)) (extract v_5320 32 64) (extract v_5320 0 32))));
      v_5335 <- eval (extract v_5314 32 64);
      v_5342 <- eval (extract v_5314 64 96);
      setRegister (lhs.of_reg v_3074) (concat (concat (concat (mux (isBitSet v_5310 4) (expression.bv_nat 32 0) (mux v_5313 v_5315 (mux v_5316 v_5315 (mux v_5317 v_5315 v_5329)))) (mux (isBitSet v_5310 5) (expression.bv_nat 32 0) (mux v_5313 v_5335 (mux v_5316 v_5335 (mux v_5317 v_5329 v_5335))))) (mux (isBitSet v_5310 6) (expression.bv_nat 32 0) (mux v_5313 v_5342 (mux v_5316 v_5329 v_5342)))) (mux (isBitSet v_5310 7) (expression.bv_nat 32 0) (mux v_5313 v_5329 (extract v_5314 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3067 : imm int) (v_3066 : Mem) (v_3068 : reg (bv 128)) => do
      v_8604 <- eval (handleImmediateWithSignExtend v_3067 8 8);
      v_8606 <- eval (extract v_8604 2 4);
      v_8607 <- eval (eq v_8606 (expression.bv_nat 2 0));
      v_8608 <- getRegister v_3068;
      v_8609 <- eval (extract v_8608 0 32);
      v_8610 <- eval (eq v_8606 (expression.bv_nat 2 1));
      v_8611 <- eval (eq v_8606 (expression.bv_nat 2 2));
      v_8612 <- evaluateAddress v_3066;
      v_8613 <- load v_8612 4;
      v_8619 <- eval (extract v_8608 32 64);
      v_8626 <- eval (extract v_8608 64 96);
      setRegister (lhs.of_reg v_3068) (concat (concat (concat (mux (isBitSet v_8604 4) (expression.bv_nat 32 0) (mux v_8607 v_8609 (mux v_8610 v_8609 (mux v_8611 v_8609 v_8613)))) (mux (isBitSet v_8604 5) (expression.bv_nat 32 0) (mux v_8607 v_8619 (mux v_8610 v_8619 (mux v_8611 v_8613 v_8619))))) (mux (isBitSet v_8604 6) (expression.bv_nat 32 0) (mux v_8607 v_8626 (mux v_8610 v_8613 v_8626)))) (mux (isBitSet v_8604 7) (expression.bv_nat 32 0) (mux v_8607 v_8613 (extract v_8608 96 128))));
      pure ()
    pat_end
