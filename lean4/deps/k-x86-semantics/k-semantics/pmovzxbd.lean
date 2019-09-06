def pmovzxbd1 : instruction :=
  definst "pmovzxbd" $ do
    pattern fun (v_2811 : reg (bv 128)) (v_2812 : reg (bv 128)) => do
      v_5555 <- getRegister v_2811;
      setRegister (lhs.of_reg v_2812) (concat (expression.bv_nat 24 0) (concat (extract v_5555 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5555 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5555 112 120) (concat (expression.bv_nat 24 0) (extract v_5555 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2807 : Mem) (v_2808 : reg (bv 128)) => do
      v_12286 <- evaluateAddress v_2807;
      v_12287 <- load v_12286 4;
      setRegister (lhs.of_reg v_2808) (concat (expression.bv_nat 24 0) (concat (extract v_12287 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12287 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12287 16 24) (concat (expression.bv_nat 24 0) (extract v_12287 24 32))))))));
      pure ()
    pat_end
