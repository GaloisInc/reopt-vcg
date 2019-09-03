def cmovnbeq1 : instruction :=
  definst "cmovnbeq" $ do
    pattern fun (v_2791 : reg (bv 64)) (v_2792 : reg (bv 64)) => do
      v_4558 <- getRegister cf;
      v_4561 <- getRegister zf;
      v_4565 <- getRegister v_2791;
      v_4566 <- getRegister v_2792;
      setRegister (lhs.of_reg v_2792) (mux (bit_and (notBool_ (eq v_4558 (expression.bv_nat 1 1))) (notBool_ (eq v_4561 (expression.bv_nat 1 1)))) v_4565 v_4566);
      pure ()
    pat_end;
    pattern fun (v_2787 : Mem) (v_2788 : reg (bv 64)) => do
      v_8145 <- getRegister cf;
      v_8148 <- getRegister zf;
      v_8152 <- evaluateAddress v_2787;
      v_8153 <- load v_8152 8;
      v_8154 <- getRegister v_2788;
      setRegister (lhs.of_reg v_2788) (mux (bit_and (notBool_ (eq v_8145 (expression.bv_nat 1 1))) (notBool_ (eq v_8148 (expression.bv_nat 1 1)))) v_8153 v_8154);
      pure ()
    pat_end
