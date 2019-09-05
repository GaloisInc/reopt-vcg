def pmovzxbd1 : instruction :=
  definst "pmovzxbd" $ do
    pattern fun (v_2783 : reg (bv 128)) (v_2784 : reg (bv 128)) => do
      v_5528 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2784) (concat (expression.bv_nat 24 0) (concat (extract v_5528 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5528 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5528 112 120) (concat (expression.bv_nat 24 0) (extract v_5528 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2780 : Mem) (v_2779 : reg (bv 128)) => do
      v_12310 <- evaluateAddress v_2780;
      v_12311 <- load v_12310 4;
      setRegister (lhs.of_reg v_2779) (concat (expression.bv_nat 24 0) (concat (extract v_12311 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12311 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12311 16 24) (concat (expression.bv_nat 24 0) (extract v_12311 24 32))))))));
      pure ()
    pat_end
