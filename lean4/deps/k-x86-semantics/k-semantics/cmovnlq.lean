def cmovnlq1 : instruction :=
  definst "cmovnlq" $ do
    pattern fun (v_3032 : reg (bv 64)) (v_3033 : reg (bv 64)) => do
      v_4895 <- getRegister sf;
      v_4897 <- getRegister of;
      v_4900 <- getRegister v_3032;
      v_4901 <- getRegister v_3033;
      setRegister (lhs.of_reg v_3033) (mux (eq (eq v_4895 (expression.bv_nat 1 1)) (eq v_4897 (expression.bv_nat 1 1))) v_4900 v_4901);
      pure ()
    pat_end;
    pattern fun (v_3027 : Mem) (v_3028 : reg (bv 64)) => do
      v_8381 <- getRegister sf;
      v_8383 <- getRegister of;
      v_8386 <- evaluateAddress v_3027;
      v_8387 <- load v_8386 8;
      v_8388 <- getRegister v_3028;
      setRegister (lhs.of_reg v_3028) (mux (eq (eq v_8381 (expression.bv_nat 1 1)) (eq v_8383 (expression.bv_nat 1 1))) v_8387 v_8388);
      pure ()
    pat_end
