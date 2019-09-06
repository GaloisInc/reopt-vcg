def pmulhuw1 : instruction :=
  definst "pmulhuw" $ do
    pattern fun (v_2883 : reg (bv 128)) (v_2884 : reg (bv 128)) => do
      v_5747 <- getRegister v_2884;
      v_5750 <- getRegister v_2883;
      setRegister (lhs.of_reg v_2884) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 0 16)) (concat (expression.bv_nat 16 0) (extract v_5750 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 16 32)) (concat (expression.bv_nat 16 0) (extract v_5750 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 32 48)) (concat (expression.bv_nat 16 0) (extract v_5750 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 48 64)) (concat (expression.bv_nat 16 0) (extract v_5750 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 64 80)) (concat (expression.bv_nat 16 0) (extract v_5750 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 80 96)) (concat (expression.bv_nat 16 0) (extract v_5750 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 96 112)) (concat (expression.bv_nat 16 0) (extract v_5750 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_5747 112 128)) (concat (expression.bv_nat 16 0) (extract v_5750 112 128))) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2879 : Mem) (v_2880 : reg (bv 128)) => do
      v_12454 <- getRegister v_2880;
      v_12457 <- evaluateAddress v_2879;
      v_12458 <- load v_12457 16;
      setRegister (lhs.of_reg v_2880) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 0 16)) (concat (expression.bv_nat 16 0) (extract v_12458 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 16 32)) (concat (expression.bv_nat 16 0) (extract v_12458 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 32 48)) (concat (expression.bv_nat 16 0) (extract v_12458 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 48 64)) (concat (expression.bv_nat 16 0) (extract v_12458 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 64 80)) (concat (expression.bv_nat 16 0) (extract v_12458 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 80 96)) (concat (expression.bv_nat 16 0) (extract v_12458 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 96 112)) (concat (expression.bv_nat 16 0) (extract v_12458 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_12454 112 128)) (concat (expression.bv_nat 16 0) (extract v_12458 112 128))) 0 16))))))));
      pure ()
    pat_end
