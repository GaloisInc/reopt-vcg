def cmovnbeq1 : instruction :=
  definst "cmovnbeq" $ do
    pattern fun (v_2843 : reg (bv 64)) (v_2844 : reg (bv 64)) => do
      v_4609 <- getRegister cf;
      v_4612 <- getRegister zf;
      v_4616 <- getRegister v_2843;
      v_4617 <- getRegister v_2844;
      setRegister (lhs.of_reg v_2844) (mux (bit_and (notBool_ (eq v_4609 (expression.bv_nat 1 1))) (notBool_ (eq v_4612 (expression.bv_nat 1 1)))) v_4616 v_4617);
      pure ()
    pat_end;
    pattern fun (v_2838 : Mem) (v_2839 : reg (bv 64)) => do
      v_8158 <- getRegister cf;
      v_8161 <- getRegister zf;
      v_8165 <- evaluateAddress v_2838;
      v_8166 <- load v_8165 8;
      v_8167 <- getRegister v_2839;
      setRegister (lhs.of_reg v_2839) (mux (bit_and (notBool_ (eq v_8158 (expression.bv_nat 1 1))) (notBool_ (eq v_8161 (expression.bv_nat 1 1)))) v_8166 v_8167);
      pure ()
    pat_end
