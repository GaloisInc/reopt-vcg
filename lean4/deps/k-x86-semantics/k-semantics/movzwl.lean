def movzwl1 : instruction :=
  definst "movzwl" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 16 0) v_3);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister r16_0;
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 16 0) v_2);
      pure ()
    pat_end
