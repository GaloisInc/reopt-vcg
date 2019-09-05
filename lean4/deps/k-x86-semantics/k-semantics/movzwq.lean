def movzwq1 : instruction :=
  definst "movzwq" $ do
    pattern fun (v_2765 : reg (bv 16)) (v_2763 : reg (bv 64)) => do
      v_4158 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2763) (concat (expression.bv_nat 48 0) v_4158);
      pure ()
    pat_end;
    pattern fun (v_2759 : Mem) (v_2760 : reg (bv 64)) => do
      v_8754 <- evaluateAddress v_2759;
      v_8755 <- load v_8754 2;
      setRegister (lhs.of_reg v_2760) (concat (expression.bv_nat 48 0) v_8755);
      pure ()
    pat_end
