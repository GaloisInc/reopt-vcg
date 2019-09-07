def cmovlw1 : instruction :=
  definst "cmovlw" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 2;
      v_6 <- getRegister r16_1;
      setRegister (lhs.of_reg r16_1) (mux (notBool_ (eq v_2 v_3)) v_5 v_6);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      v_4 <- getRegister r16_0;
      v_5 <- getRegister r16_1;
      setRegister (lhs.of_reg r16_1) (mux (notBool_ (eq v_2 v_3)) v_4 v_5);
      pure ()
    pat_end
