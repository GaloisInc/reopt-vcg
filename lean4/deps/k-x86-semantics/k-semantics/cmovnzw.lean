def cmovnzw1 : instruction :=
  definst "cmovnzw" $ do
    pattern fun (v_3123 : reg (bv 16)) (v_3124 : reg (bv 16)) => do
      v_5006 <- getRegister zf;
      v_5009 <- getRegister v_3123;
      v_5010 <- getRegister v_3124;
      setRegister (lhs.of_reg v_3124) (mux (notBool_ (eq v_5006 (expression.bv_nat 1 1))) v_5009 v_5010);
      pure ()
    pat_end;
    pattern fun (v_3117 : Mem) (v_3119 : reg (bv 16)) => do
      v_8479 <- getRegister zf;
      v_8482 <- evaluateAddress v_3117;
      v_8483 <- load v_8482 2;
      v_8484 <- getRegister v_3119;
      setRegister (lhs.of_reg v_3119) (mux (notBool_ (eq v_8479 (expression.bv_nat 1 1))) v_8483 v_8484);
      pure ()
    pat_end
