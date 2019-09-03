def movzwq1 : instruction :=
  definst "movzwq" $ do
    pattern fun (v_2701 : reg (bv 16)) (v_2702 : reg (bv 64)) => do
      v_4094 <- getRegister v_2701;
      setRegister (lhs.of_reg v_2702) (concat (expression.bv_nat 48 0) v_4094);
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) (v_2697 : reg (bv 64)) => do
      v_8911 <- evaluateAddress v_2696;
      v_8912 <- load v_8911 2;
      setRegister (lhs.of_reg v_2697) (concat (expression.bv_nat 48 0) v_8912);
      pure ()
    pat_end
