def pmovzxwq1 : instruction :=
  definst "pmovzxwq" $ do
    pattern fun (v_2856 : reg (bv 128)) (v_2857 : reg (bv 128)) => do
      v_5640 <- getRegister v_2856;
      setRegister (lhs.of_reg v_2857) (concat (expression.bv_nat 48 0) (concat (extract v_5640 96 112) (concat (expression.bv_nat 48 0) (extract v_5640 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2852 : Mem) (v_2853 : reg (bv 128)) => do
      v_12356 <- evaluateAddress v_2852;
      v_12357 <- load v_12356 4;
      setRegister (lhs.of_reg v_2853) (concat (expression.bv_nat 48 0) (concat (extract v_12357 0 16) (concat (expression.bv_nat 48 0) (extract v_12357 16 32))));
      pure ()
    pat_end
