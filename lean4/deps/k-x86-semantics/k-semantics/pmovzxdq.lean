def pmovzxdq1 : instruction :=
  definst "pmovzxdq" $ do
    pattern fun (v_2747 : reg (bv 128)) (v_2748 : reg (bv 128)) => do
      v_5643 <- getRegister v_2747;
      setRegister (lhs.of_reg v_2748) (concat (expression.bv_nat 32 0) (concat (extract v_5643 64 96) (concat (expression.bv_nat 32 0) (extract v_5643 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2742 : Mem) (v_2743 : reg (bv 128)) => do
      v_12915 <- evaluateAddress v_2742;
      v_12916 <- load v_12915 8;
      setRegister (lhs.of_reg v_2743) (concat (expression.bv_nat 32 0) (concat (extract v_12916 0 32) (concat (expression.bv_nat 32 0) (extract v_12916 32 64))));
      pure ()
    pat_end
