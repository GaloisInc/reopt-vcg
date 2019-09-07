def cmovns1 : instruction :=
  definst "cmovns" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister sf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 2;
      v_5 <- getRegister r16_1;
      setRegister (lhs.of_reg r16_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister sf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      v_5 <- getRegister r32_1;
      setRegister (lhs.of_reg r32_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister sf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- getRegister r64_1;
      setRegister (lhs.of_reg r64_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
    pat_end
