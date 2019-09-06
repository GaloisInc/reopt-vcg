def movzwq1 : instruction :=
  definst "movzwq" $ do
    pattern fun (v_2790 : reg (bv 16)) (v_2789 : reg (bv 64)) => do
      v_4185 <- getRegister v_2790;
      setRegister (lhs.of_reg v_2789) (concat (expression.bv_nat 48 0) v_4185);
      pure ()
    pat_end;
    pattern fun (v_2785 : Mem) (v_2786 : reg (bv 64)) => do
      v_8781 <- evaluateAddress v_2785;
      v_8782 <- load v_8781 2;
      setRegister (lhs.of_reg v_2786) (concat (expression.bv_nat 48 0) v_8782);
      pure ()
    pat_end
