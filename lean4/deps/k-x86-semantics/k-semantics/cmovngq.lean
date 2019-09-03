def cmovngq1 : instruction :=
  definst "cmovngq" $ do
    pattern fun (v_2926 : reg (bv 64)) (v_2927 : reg (bv 64)) => do
      v_4746 <- getRegister zf;
      v_4748 <- getRegister sf;
      v_4750 <- getRegister of;
      v_4755 <- getRegister v_2926;
      v_4756 <- getRegister v_2927;
      setRegister (lhs.of_reg v_2927) (mux (bit_or (eq v_4746 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4748 (expression.bv_nat 1 1)) (eq v_4750 (expression.bv_nat 1 1))))) v_4755 v_4756);
      pure ()
    pat_end;
    pattern fun (v_2922 : Mem) (v_2923 : reg (bv 64)) => do
      v_8288 <- getRegister zf;
      v_8290 <- getRegister sf;
      v_8292 <- getRegister of;
      v_8297 <- evaluateAddress v_2922;
      v_8298 <- load v_8297 8;
      v_8299 <- getRegister v_2923;
      setRegister (lhs.of_reg v_2923) (mux (bit_or (eq v_8288 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8290 (expression.bv_nat 1 1)) (eq v_8292 (expression.bv_nat 1 1))))) v_8298 v_8299);
      pure ()
    pat_end
