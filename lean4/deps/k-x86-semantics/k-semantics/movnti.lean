def movnti1 : instruction :=
  definst "movnti" $ do
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r32_0;
      store v_2 v_3 4;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r64_0;
      store v_2 v_3 8;
      pure ()
    pat_end
