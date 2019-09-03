def pmovzxdq1 : instruction :=
  definst "pmovzxdq" $ do
    pattern fun (v_2761 : reg (bv 128)) (v_2762 : reg (bv 128)) => do
      v_5554 <- getRegister v_2761;
      setRegister (lhs.of_reg v_2762) (concat (expression.bv_nat 32 0) (concat (extract v_5554 64 96) (concat (expression.bv_nat 32 0) (extract v_5554 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2757 : Mem) (v_2758 : reg (bv 128)) => do
      v_12500 <- evaluateAddress v_2757;
      v_12501 <- load v_12500 8;
      setRegister (lhs.of_reg v_2758) (concat (expression.bv_nat 32 0) (concat (extract v_12501 0 32) (concat (expression.bv_nat 32 0) (extract v_12501 32 64))));
      pure ()
    pat_end
