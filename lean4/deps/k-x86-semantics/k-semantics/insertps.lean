def insertps1 : instruction :=
  definst "insertps" $ do
    pattern fun (v_3009 : imm int) (v_3007 : reg (bv 128)) (v_3008 : reg (bv 128)) => do
      v_5392 <- eval (handleImmediateWithSignExtend v_3009 8 8);
      v_5395 <- eval (extract v_5392 2 4);
      v_5396 <- eval (eq v_5395 (expression.bv_nat 2 0));
      v_5397 <- getRegister v_3008;
      v_5398 <- eval (extract v_5397 0 32);
      v_5399 <- eval (eq v_5395 (expression.bv_nat 2 1));
      v_5400 <- eval (eq v_5395 (expression.bv_nat 2 2));
      v_5401 <- eval (extract v_5392 0 2);
      v_5403 <- getRegister v_3007;
      v_5412 <- eval (mux (eq v_5401 (expression.bv_nat 2 0)) (extract v_5403 96 128) (mux (eq v_5401 (expression.bv_nat 2 1)) (extract v_5403 64 96) (mux (eq v_5401 (expression.bv_nat 2 2)) (extract v_5403 32 64) (extract v_5403 0 32))));
      v_5419 <- eval (extract v_5397 32 64);
      v_5427 <- eval (extract v_5397 64 96);
      setRegister (lhs.of_reg v_3008) (concat (concat (concat (mux (eq (extract v_5392 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5396 v_5398 (mux v_5399 v_5398 (mux v_5400 v_5398 v_5412)))) (mux (eq (extract v_5392 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5396 v_5419 (mux v_5399 v_5419 (mux v_5400 v_5412 v_5419))))) (mux (eq (extract v_5392 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5396 v_5427 (mux v_5399 v_5412 v_5427)))) (mux (eq (extract v_5392 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5396 v_5412 (extract v_5397 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3004 : imm int) (v_3002 : Mem) (v_3003 : reg (bv 128)) => do
      v_8878 <- eval (handleImmediateWithSignExtend v_3004 8 8);
      v_8881 <- eval (extract v_8878 2 4);
      v_8882 <- eval (eq v_8881 (expression.bv_nat 2 0));
      v_8883 <- getRegister v_3003;
      v_8884 <- eval (extract v_8883 0 32);
      v_8885 <- eval (eq v_8881 (expression.bv_nat 2 1));
      v_8886 <- eval (eq v_8881 (expression.bv_nat 2 2));
      v_8887 <- evaluateAddress v_3002;
      v_8888 <- load v_8887 4;
      v_8895 <- eval (extract v_8883 32 64);
      v_8903 <- eval (extract v_8883 64 96);
      setRegister (lhs.of_reg v_3003) (concat (concat (concat (mux (eq (extract v_8878 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_8882 v_8884 (mux v_8885 v_8884 (mux v_8886 v_8884 v_8888)))) (mux (eq (extract v_8878 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_8882 v_8895 (mux v_8885 v_8895 (mux v_8886 v_8888 v_8895))))) (mux (eq (extract v_8878 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_8882 v_8903 (mux v_8885 v_8888 v_8903)))) (mux (eq (extract v_8878 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_8882 v_8888 (extract v_8883 96 128))));
      pure ()
    pat_end
