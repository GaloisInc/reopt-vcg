def cmovlel1 : instruction :=
  definst "cmovlel" $ do
    pattern fun (v_2646 : reg (bv 32)) (v_2647 : reg (bv 32)) => do
      v_4358 <- getRegister zf;
      v_4360 <- getRegister sf;
      v_4362 <- getRegister of;
      v_4367 <- getRegister v_2646;
      v_4368 <- getRegister v_2647;
      setRegister (lhs.of_reg v_2647) (mux (bit_or (eq v_4358 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4360 (expression.bv_nat 1 1)) (eq v_4362 (expression.bv_nat 1 1))))) v_4367 v_4368);
      pure ()
    pat_end;
    pattern fun (v_2638 : Mem) (v_2639 : reg (bv 32)) => do
      v_8032 <- getRegister zf;
      v_8034 <- getRegister sf;
      v_8036 <- getRegister of;
      v_8041 <- evaluateAddress v_2638;
      v_8042 <- load v_8041 4;
      v_8043 <- getRegister v_2639;
      setRegister (lhs.of_reg v_2639) (mux (bit_or (eq v_8032 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8034 (expression.bv_nat 1 1)) (eq v_8036 (expression.bv_nat 1 1))))) v_8042 v_8043);
      pure ()
    pat_end
