def movzbw1 : instruction :=
  definst "movzbw" $ do
    pattern fun (v_2771 : reg (bv 8)) (v_2772 : reg (bv 16)) => do
      v_4171 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2772) (concat (expression.bv_nat 8 0) v_4171);
      pure ()
    pat_end;
    pattern fun (v_2762 : Mem) (v_2763 : reg (bv 16)) => do
      v_8773 <- evaluateAddress v_2762;
      v_8774 <- load v_8773 1;
      setRegister (lhs.of_reg v_2763) (concat (expression.bv_nat 8 0) v_8774);
      pure ()
    pat_end
