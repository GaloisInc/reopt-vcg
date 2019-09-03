def vinsertps1 : instruction :=
  definst "vinsertps" $ do
    pattern fun (v_2478 : imm int) (v_2480 : reg (bv 128)) (v_2481 : reg (bv 128)) (v_2482 : reg (bv 128)) => do
      v_4218 <- eval (handleImmediateWithSignExtend v_2478 8 8);
      v_4221 <- eval (extract v_4218 2 4);
      v_4222 <- eval (eq v_4221 (expression.bv_nat 2 0));
      v_4223 <- getRegister v_2481;
      v_4224 <- eval (extract v_4223 0 32);
      v_4225 <- eval (eq v_4221 (expression.bv_nat 2 1));
      v_4226 <- eval (eq v_4221 (expression.bv_nat 2 2));
      v_4227 <- eval (extract v_4218 0 2);
      v_4229 <- getRegister v_2480;
      v_4238 <- eval (mux (eq v_4227 (expression.bv_nat 2 0)) (extract v_4229 96 128) (mux (eq v_4227 (expression.bv_nat 2 1)) (extract v_4229 64 96) (mux (eq v_4227 (expression.bv_nat 2 2)) (extract v_4229 32 64) (extract v_4229 0 32))));
      v_4245 <- eval (extract v_4223 32 64);
      v_4253 <- eval (extract v_4223 64 96);
      setRegister (lhs.of_reg v_2482) (concat (concat (concat (mux (eq (extract v_4218 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4222 v_4224 (mux v_4225 v_4224 (mux v_4226 v_4224 v_4238)))) (mux (eq (extract v_4218 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4222 v_4245 (mux v_4225 v_4245 (mux v_4226 v_4238 v_4245))))) (mux (eq (extract v_4218 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4222 v_4253 (mux v_4225 v_4238 v_4253)))) (mux (eq (extract v_4218 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4222 v_4238 (extract v_4223 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2472 : imm int) (v_2473 : Mem) (v_2474 : reg (bv 128)) (v_2475 : reg (bv 128)) => do
      v_9829 <- eval (handleImmediateWithSignExtend v_2472 8 8);
      v_9832 <- eval (extract v_9829 2 4);
      v_9833 <- eval (eq v_9832 (expression.bv_nat 2 0));
      v_9834 <- getRegister v_2474;
      v_9835 <- eval (extract v_9834 0 32);
      v_9836 <- eval (eq v_9832 (expression.bv_nat 2 1));
      v_9837 <- eval (eq v_9832 (expression.bv_nat 2 2));
      v_9838 <- evaluateAddress v_2473;
      v_9839 <- load v_9838 4;
      v_9846 <- eval (extract v_9834 32 64);
      v_9854 <- eval (extract v_9834 64 96);
      setRegister (lhs.of_reg v_2475) (concat (concat (concat (mux (eq (extract v_9829 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9833 v_9835 (mux v_9836 v_9835 (mux v_9837 v_9835 v_9839)))) (mux (eq (extract v_9829 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9833 v_9846 (mux v_9836 v_9846 (mux v_9837 v_9839 v_9846))))) (mux (eq (extract v_9829 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9833 v_9854 (mux v_9836 v_9839 v_9854)))) (mux (eq (extract v_9829 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9833 v_9839 (extract v_9834 96 128))));
      pure ()
    pat_end
