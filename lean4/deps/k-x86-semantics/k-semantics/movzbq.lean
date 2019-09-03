def movzbq1 : instruction :=
  definst "movzbq" $ do
    pattern fun (v_2669 : reg (bv 8)) (v_2670 : reg (bv 64)) => do
      v_4070 <- getRegister v_2669;
      setRegister (lhs.of_reg v_2670) (concat (expression.bv_nat 56 0) v_4070);
      pure ()
    pat_end;
    pattern fun (v_2664 : Mem) (v_2665 : reg (bv 64)) => do
      v_8899 <- evaluateAddress v_2664;
      v_8900 <- load v_8899 1;
      setRegister (lhs.of_reg v_2665) (concat (expression.bv_nat 56 0) v_8900);
      pure ()
    pat_end
