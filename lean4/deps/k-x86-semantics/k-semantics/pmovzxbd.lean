def pmovzxbd1 : instruction :=
  definst "pmovzxbd" $ do
    pattern fun (v_2734 : reg (bv 128)) (v_2735 : reg (bv 128)) => do
      v_5497 <- getRegister v_2734;
      setRegister (lhs.of_reg v_2735) (concat (expression.bv_nat 24 0) (concat (extract v_5497 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5497 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5497 112 120) (concat (expression.bv_nat 24 0) (extract v_5497 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2730 : Mem) (v_2731 : reg (bv 128)) => do
      v_12452 <- evaluateAddress v_2730;
      v_12453 <- load v_12452 4;
      setRegister (lhs.of_reg v_2731) (concat (expression.bv_nat 24 0) (concat (extract v_12453 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12453 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12453 16 24) (concat (expression.bv_nat 24 0) (extract v_12453 24 32))))))));
      pure ()
    pat_end
