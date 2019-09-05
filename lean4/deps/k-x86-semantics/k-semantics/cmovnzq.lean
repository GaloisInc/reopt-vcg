def cmovnzq1 : instruction :=
  definst "cmovnzq" $ do
    pattern fun (v_3164 : reg (bv 64)) (v_3165 : reg (bv 64)) => do
      v_5046 <- getRegister zf;
      v_5049 <- getRegister v_3164;
      v_5050 <- getRegister v_3165;
      setRegister (lhs.of_reg v_3165) (mux (notBool_ (eq v_5046 (expression.bv_nat 1 1))) v_5049 v_5050);
      pure ()
    pat_end;
    pattern fun (v_3159 : Mem) (v_3160 : reg (bv 64)) => do
      v_8484 <- getRegister zf;
      v_8487 <- evaluateAddress v_3159;
      v_8488 <- load v_8487 8;
      v_8489 <- getRegister v_3160;
      setRegister (lhs.of_reg v_3160) (mux (notBool_ (eq v_8484 (expression.bv_nat 1 1))) v_8488 v_8489);
      pure ()
    pat_end
