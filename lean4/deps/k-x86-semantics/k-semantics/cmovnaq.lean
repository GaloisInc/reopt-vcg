def cmovnaq1 : instruction :=
  definst "cmovnaq" $ do
    pattern fun (v_2753 : reg (bv 64)) (v_2754 : reg (bv 64)) => do
      v_4504 <- getRegister cf;
      v_4506 <- getRegister zf;
      v_4509 <- getRegister v_2753;
      v_4510 <- getRegister v_2754;
      setRegister (lhs.of_reg v_2754) (mux (bit_or (eq v_4504 (expression.bv_nat 1 1)) (eq v_4506 (expression.bv_nat 1 1))) v_4509 v_4510);
      pure ()
    pat_end;
    pattern fun (v_2748 : Mem) (v_2749 : reg (bv 64)) => do
      v_8140 <- getRegister cf;
      v_8142 <- getRegister zf;
      v_8145 <- evaluateAddress v_2748;
      v_8146 <- load v_8145 8;
      v_8147 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2749) (mux (bit_or (eq v_8140 (expression.bv_nat 1 1)) (eq v_8142 (expression.bv_nat 1 1))) v_8146 v_8147);
      pure ()
    pat_end
