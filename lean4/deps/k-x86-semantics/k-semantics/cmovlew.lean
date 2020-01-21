def cmovlew : instruction :=
  definst "cmovlew" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister zf;
      v_3 <- getRegister sf;
      v_4 <- getRegister of;
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 2;
      v_7 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux (bit_or v_2 (notBool_ (eq v_3 v_4))) v_6 v_7);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister zf;
      v_3 <- getRegister sf;
      v_4 <- getRegister of;
      v_5 <- getRegister (lhs.of_reg r16_0);
      v_6 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux (bit_or v_2 (notBool_ (eq v_3 v_4))) v_5 v_6);
      pure ()
    pat_end
