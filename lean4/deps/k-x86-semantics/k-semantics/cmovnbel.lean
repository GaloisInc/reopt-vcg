def cmovnbel1 : instruction :=
  definst "cmovnbel" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister zf;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      v_6 <- getRegister r32_1;
      setRegister (lhs.of_reg r32_1) (mux (bit_and (notBool_ v_2) (notBool_ v_3)) v_5 v_6);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister zf;
      v_4 <- getRegister r32_0;
      v_5 <- getRegister r32_1;
      setRegister (lhs.of_reg r32_1) (mux (bit_and (notBool_ v_2) (notBool_ v_3)) v_4 v_5);
      pure ()
    pat_end
