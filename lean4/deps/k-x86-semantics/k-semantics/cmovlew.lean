def cmovlew1 : instruction :=
  definst "cmovlew" $ do
    pattern fun (v_2744 : reg (bv 16)) (v_2745 : reg (bv 16)) => do
      v_4466 <- getRegister zf;
      v_4468 <- getRegister sf;
      v_4470 <- getRegister of;
      v_4475 <- getRegister v_2744;
      v_4476 <- getRegister v_2745;
      setRegister (lhs.of_reg v_2745) (mux (bit_or (eq v_4466 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4468 (expression.bv_nat 1 1)) (eq v_4470 (expression.bv_nat 1 1))))) v_4475 v_4476);
      pure ()
    pat_end;
    pattern fun (v_2735 : Mem) (v_2736 : reg (bv 16)) => do
      v_8048 <- getRegister zf;
      v_8050 <- getRegister sf;
      v_8052 <- getRegister of;
      v_8057 <- evaluateAddress v_2735;
      v_8058 <- load v_8057 2;
      v_8059 <- getRegister v_2736;
      setRegister (lhs.of_reg v_2736) (mux (bit_or (eq v_8048 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8050 (expression.bv_nat 1 1)) (eq v_8052 (expression.bv_nat 1 1))))) v_8058 v_8059);
      pure ()
    pat_end
