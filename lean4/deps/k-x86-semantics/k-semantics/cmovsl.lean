def cmovsl1 : instruction :=
  definst "cmovsl" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister sf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      v_5 <- getRegister r32_1;
      setRegister (lhs.of_reg r32_1) (mux v_2 v_4 v_5);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister r32_0;
      v_4 <- getRegister r32_1;
      setRegister (lhs.of_reg r32_1) (mux v_2 v_3 v_4);
      pure ()
    pat_end
