def movzwq1 : instruction :=
  definst "movzwq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 48 0) v_3);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r16_0;
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 48 0) v_2);
      pure ()
    pat_end
