def sarx1 : instruction :=
  definst "sarx" $ do
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 4;
      v_5 <- getRegister r32_0;
      setRegister (lhs.of_reg r32_2) (ashr v_4 (bv_and v_5 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister r32_1;
      v_4 <- getRegister r32_0;
      setRegister (lhs.of_reg r32_2) (ashr v_3 (bv_and v_4 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 8;
      v_5 <- getRegister r64_0;
      setRegister (lhs.of_reg r64_2) (ashr v_4 (bv_and v_5 (expression.bv_nat 64 63)));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister r64_1;
      v_4 <- getRegister r64_0;
      setRegister (lhs.of_reg r64_2) (ashr v_3 (bv_and v_4 (expression.bv_nat 64 63)));
      pure ()
    pat_end
