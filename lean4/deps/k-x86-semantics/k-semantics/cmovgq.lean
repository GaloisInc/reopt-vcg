def cmovgq1 : instruction :=
  definst "cmovgq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister zf;
      v_3 <- getRegister sf;
      v_4 <- getRegister of;
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 8;
      v_7 <- getRegister r64_1;
      setRegister (lhs.of_reg r64_1) (mux (bit_and (notBool_ v_2) (eq v_3 v_4)) v_6 v_7);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister zf;
      v_3 <- getRegister sf;
      v_4 <- getRegister of;
      v_5 <- getRegister r64_0;
      v_6 <- getRegister r64_1;
      setRegister (lhs.of_reg r64_1) (mux (bit_and (notBool_ v_2) (eq v_3 v_4)) v_5 v_6);
      pure ()
    pat_end
