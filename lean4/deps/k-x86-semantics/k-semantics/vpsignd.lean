def vpsignd1 : instruction :=
  definst "vpsignd" $ do
    pattern fun (v_3109 : reg (bv 128)) (v_3110 : reg (bv 128)) (v_3111 : reg (bv 128)) => do
      v_7559 <- getRegister v_3109;
      v_7560 <- eval (extract v_7559 0 32);
      v_7562 <- getRegister v_3110;
      v_7563 <- eval (extract v_7562 0 32);
      v_7569 <- eval (extract v_7559 32 64);
      v_7571 <- eval (extract v_7562 32 64);
      v_7577 <- eval (extract v_7559 64 96);
      v_7579 <- eval (extract v_7562 64 96);
      v_7585 <- eval (extract v_7559 96 128);
      v_7587 <- eval (extract v_7562 96 128);
      setRegister (lhs.of_reg v_3111) (concat (mux (sgt v_7560 (expression.bv_nat 32 0)) v_7563 (mux (eq v_7560 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7563 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7569 (expression.bv_nat 32 0)) v_7571 (mux (eq v_7569 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7571 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7577 (expression.bv_nat 32 0)) v_7579 (mux (eq v_7577 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7579 (expression.bv_nat 32 4294967295))))) (mux (sgt v_7585 (expression.bv_nat 32 0)) v_7587 (mux (eq v_7585 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7587 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end;
    pattern fun (v_3103 : Mem) (v_3104 : reg (bv 128)) (v_3105 : reg (bv 128)) => do
      v_13841 <- evaluateAddress v_3103;
      v_13842 <- load v_13841 16;
      v_13843 <- eval (extract v_13842 0 32);
      v_13845 <- getRegister v_3104;
      v_13846 <- eval (extract v_13845 0 32);
      v_13852 <- eval (extract v_13842 32 64);
      v_13854 <- eval (extract v_13845 32 64);
      v_13860 <- eval (extract v_13842 64 96);
      v_13862 <- eval (extract v_13845 64 96);
      v_13868 <- eval (extract v_13842 96 128);
      v_13870 <- eval (extract v_13845 96 128);
      setRegister (lhs.of_reg v_3105) (concat (mux (sgt v_13843 (expression.bv_nat 32 0)) v_13846 (mux (eq v_13843 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13846 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_13852 (expression.bv_nat 32 0)) v_13854 (mux (eq v_13852 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13854 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_13860 (expression.bv_nat 32 0)) v_13862 (mux (eq v_13860 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13862 (expression.bv_nat 32 4294967295))))) (mux (sgt v_13868 (expression.bv_nat 32 0)) v_13870 (mux (eq v_13868 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13870 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end
