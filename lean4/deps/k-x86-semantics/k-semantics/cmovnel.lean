def cmovnel1 : instruction :=
  definst "cmovnel" $ do
    pattern fun (v_2863 : reg (bv 32)) (v_2864 : reg (bv 32)) => do
      v_4654 <- getRegister zf;
      v_4657 <- getRegister v_2863;
      v_4658 <- getRegister v_2864;
      setRegister (lhs.of_reg v_2864) (mux (notBool_ (eq v_4654 (expression.bv_nat 1 1))) v_4657 v_4658);
      pure ()
    pat_end;
    pattern fun (v_2859 : Mem) (v_2860 : reg (bv 32)) => do
      v_8217 <- getRegister zf;
      v_8220 <- evaluateAddress v_2859;
      v_8221 <- load v_8220 4;
      v_8222 <- getRegister v_2860;
      setRegister (lhs.of_reg v_2860) (mux (notBool_ (eq v_8217 (expression.bv_nat 1 1))) v_8221 v_8222);
      pure ()
    pat_end
