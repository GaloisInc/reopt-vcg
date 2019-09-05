def cmovaw1 : instruction :=
  definst "cmovaw" $ do
    pattern fun (v_2483 : reg (bv 16)) (v_2484 : reg (bv 16)) => do
      v_4153 <- getRegister cf;
      v_4156 <- getRegister zf;
      v_4160 <- getRegister v_2483;
      v_4161 <- getRegister v_2484;
      setRegister (lhs.of_reg v_2484) (mux (bit_and (notBool_ (eq v_4153 (expression.bv_nat 1 1))) (notBool_ (eq v_4156 (expression.bv_nat 1 1)))) v_4160 v_4161);
      pure ()
    pat_end;
    pattern fun (v_2478 : Mem) (v_2479 : reg (bv 16)) => do
      v_7834 <- getRegister cf;
      v_7837 <- getRegister zf;
      v_7841 <- evaluateAddress v_2478;
      v_7842 <- load v_7841 2;
      v_7843 <- getRegister v_2479;
      setRegister (lhs.of_reg v_2479) (mux (bit_and (notBool_ (eq v_7834 (expression.bv_nat 1 1))) (notBool_ (eq v_7837 (expression.bv_nat 1 1)))) v_7842 v_7843);
      pure ()
    pat_end
