def movzbw : instruction :=
  definst "movzbw" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 1;
      setRegister (lhs.of_reg r16_1) (concat (expression.bv_nat 8 0) v_3);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg rh_0);
      setRegister (lhs.of_reg r16_1) (concat (expression.bv_nat 8 0) v_2);
      pure ()
    pat_end
