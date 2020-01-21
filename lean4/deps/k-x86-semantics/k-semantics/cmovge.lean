def cmovge : instruction :=
  definst "cmovge" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 2;
      v_6 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux (eq v_2 v_3) v_5 v_6);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      v_6 <- getRegister (lhs.of_reg r32_1);
      setRegister (lhs.of_reg r32_1) (mux (eq v_2 v_3) v_5 v_6);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      v_6 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (eq v_2 v_3) v_5 v_6);
      pure ()
    pat_end
