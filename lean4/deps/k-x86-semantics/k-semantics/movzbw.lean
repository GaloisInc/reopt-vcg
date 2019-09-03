def movzbw1 : instruction :=
  definst "movzbw" $ do
    pattern fun (v_2678 : reg (bv 8)) (v_2679 : reg (bv 16)) => do
      v_4077 <- getRegister v_2678;
      setRegister (lhs.of_reg v_2679) (concat (expression.bv_nat 8 0) v_4077);
      pure ()
    pat_end;
    pattern fun (v_2673 : Mem) (v_2674 : reg (bv 16)) => do
      v_8903 <- evaluateAddress v_2673;
      v_8904 <- load v_8903 1;
      setRegister (lhs.of_reg v_2674) (concat (expression.bv_nat 8 0) v_8904);
      pure ()
    pat_end
