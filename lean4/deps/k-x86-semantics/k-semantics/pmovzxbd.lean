def pmovzxbd1 : instruction :=
  definst "pmovzxbd" $ do
    pattern fun (v_2720 : reg (bv 128)) (v_2721 : reg (bv 128)) => do
      v_5586 <- getRegister v_2720;
      setRegister (lhs.of_reg v_2721) (concat (expression.bv_nat 24 0) (concat (extract v_5586 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5586 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5586 112 120) (concat (expression.bv_nat 24 0) (extract v_5586 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2715 : Mem) (v_2716 : reg (bv 128)) => do
      v_12867 <- evaluateAddress v_2715;
      v_12868 <- load v_12867 4;
      setRegister (lhs.of_reg v_2716) (concat (expression.bv_nat 24 0) (concat (extract v_12868 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12868 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12868 16 24) (concat (expression.bv_nat 24 0) (extract v_12868 24 32))))))));
      pure ()
    pat_end
