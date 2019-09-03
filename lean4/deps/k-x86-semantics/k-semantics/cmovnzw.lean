def cmovnzw1 : instruction :=
  definst "cmovnzw" $ do
    pattern fun (v_3109 : reg (bv 16)) (v_3110 : reg (bv 16)) => do
      v_4993 <- getRegister zf;
      v_4996 <- getRegister v_3109;
      v_4997 <- getRegister v_3110;
      setRegister (lhs.of_reg v_3110) (mux (notBool_ (eq v_4993 (expression.bv_nat 1 1))) v_4996 v_4997);
      pure ()
    pat_end;
    pattern fun (v_3106 : Mem) (v_3105 : reg (bv 16)) => do
      v_8506 <- getRegister zf;
      v_8509 <- evaluateAddress v_3106;
      v_8510 <- load v_8509 2;
      v_8511 <- getRegister v_3105;
      setRegister (lhs.of_reg v_3105) (mux (notBool_ (eq v_8506 (expression.bv_nat 1 1))) v_8510 v_8511);
      pure ()
    pat_end
