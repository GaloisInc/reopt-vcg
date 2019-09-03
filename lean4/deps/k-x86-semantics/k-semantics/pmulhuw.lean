def pmulhuw1 : instruction :=
  definst "pmulhuw" $ do
    pattern fun (v_2806 : reg (bv 128)) (v_2807 : reg (bv 128)) => do
      v_5689 <- getRegister v_2807;
      v_5692 <- getRegister v_2806;
      setRegister (lhs.of_reg v_2807) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 0 16)) (concat (expression.bv_nat 16 0) (extract v_5692 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 16 32)) (concat (expression.bv_nat 16 0) (extract v_5692 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 32 48)) (concat (expression.bv_nat 16 0) (extract v_5692 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 48 64)) (concat (expression.bv_nat 16 0) (extract v_5692 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 64 80)) (concat (expression.bv_nat 16 0) (extract v_5692 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 80 96)) (concat (expression.bv_nat 16 0) (extract v_5692 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 96 112)) (concat (expression.bv_nat 16 0) (extract v_5692 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_5689 112 128)) (concat (expression.bv_nat 16 0) (extract v_5692 112 128))) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2802 : Mem) (v_2803 : reg (bv 128)) => do
      v_12620 <- getRegister v_2803;
      v_12623 <- evaluateAddress v_2802;
      v_12624 <- load v_12623 16;
      setRegister (lhs.of_reg v_2803) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 0 16)) (concat (expression.bv_nat 16 0) (extract v_12624 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 16 32)) (concat (expression.bv_nat 16 0) (extract v_12624 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 32 48)) (concat (expression.bv_nat 16 0) (extract v_12624 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 48 64)) (concat (expression.bv_nat 16 0) (extract v_12624 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 64 80)) (concat (expression.bv_nat 16 0) (extract v_12624 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 80 96)) (concat (expression.bv_nat 16 0) (extract v_12624 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 96 112)) (concat (expression.bv_nat 16 0) (extract v_12624 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_12620 112 128)) (concat (expression.bv_nat 16 0) (extract v_12624 112 128))) 0 16))))))));
      pure ()
    pat_end
