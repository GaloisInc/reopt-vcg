def cmovpow1 : instruction :=
  definst "cmovpow" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister pf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 2;
      v_5 <- getRegister r16_1;
      setRegister (lhs.of_reg r16_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister pf;
      v_3 <- getRegister r16_0;
      v_4 <- getRegister r16_1;
      setRegister (lhs.of_reg r16_1) (mux (notBool_ v_2) v_3 v_4);
      pure ()
    pat_end
