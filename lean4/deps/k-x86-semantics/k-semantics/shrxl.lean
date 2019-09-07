def shrxl1 : instruction :=
  definst "shrxl" $ do
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 4;
      v_5 <- getRegister r32_0;
      setRegister (lhs.of_reg r32_2) (lshr v_4 (bv_and v_5 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister r32_1;
      v_4 <- getRegister r32_0;
      setRegister (lhs.of_reg r32_2) (lshr v_3 (bv_and v_4 (expression.bv_nat 32 31)));
      pure ()
    pat_end
