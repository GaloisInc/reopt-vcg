def pmovzxbq1 : instruction :=
  definst "pmovzxbq" $ do
    pattern fun (v_2743 : reg (bv 128)) (v_2744 : reg (bv 128)) => do
      v_5514 <- getRegister v_2743;
      setRegister (lhs.of_reg v_2744) (concat (expression.bv_nat 56 0) (concat (extract v_5514 112 120) (concat (expression.bv_nat 56 0) (extract v_5514 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2739 : Mem) (v_2740 : reg (bv 128)) => do
      v_12466 <- evaluateAddress v_2739;
      v_12467 <- load v_12466 2;
      setRegister (lhs.of_reg v_2740) (concat (expression.bv_nat 56 0) (concat (extract v_12467 0 8) (concat (expression.bv_nat 56 0) (extract v_12467 8 16))));
      pure ()
    pat_end
