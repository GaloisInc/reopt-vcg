def pmovzxwq1 : instruction :=
  definst "pmovzxwq" $ do
    pattern fun (v_2828 : reg (bv 128)) (v_2829 : reg (bv 128)) => do
      v_5613 <- getRegister v_2828;
      setRegister (lhs.of_reg v_2829) (concat (expression.bv_nat 48 0) (concat (extract v_5613 96 112) (concat (expression.bv_nat 48 0) (extract v_5613 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2825 : Mem) (v_2824 : reg (bv 128)) => do
      v_12380 <- evaluateAddress v_2825;
      v_12381 <- load v_12380 4;
      setRegister (lhs.of_reg v_2824) (concat (expression.bv_nat 48 0) (concat (extract v_12381 0 16) (concat (expression.bv_nat 48 0) (extract v_12381 16 32))));
      pure ()
    pat_end
