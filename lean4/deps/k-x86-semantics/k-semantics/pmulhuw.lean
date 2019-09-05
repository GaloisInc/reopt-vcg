def pmulhuw1 : instruction :=
  definst "pmulhuw" $ do
    pattern fun (v_2855 : reg (bv 128)) (v_2856 : reg (bv 128)) => do
      v_5720 <- getRegister v_2856;
      v_5723 <- getRegister v_2855;
      setRegister (lhs.of_reg v_2856) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 0 16)) (concat (expression.bv_nat 16 0) (extract v_5723 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 16 32)) (concat (expression.bv_nat 16 0) (extract v_5723 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 32 48)) (concat (expression.bv_nat 16 0) (extract v_5723 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 48 64)) (concat (expression.bv_nat 16 0) (extract v_5723 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 64 80)) (concat (expression.bv_nat 16 0) (extract v_5723 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 80 96)) (concat (expression.bv_nat 16 0) (extract v_5723 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 96 112)) (concat (expression.bv_nat 16 0) (extract v_5723 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_5720 112 128)) (concat (expression.bv_nat 16 0) (extract v_5723 112 128))) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2852 : Mem) (v_2851 : reg (bv 128)) => do
      v_12478 <- getRegister v_2851;
      v_12481 <- evaluateAddress v_2852;
      v_12482 <- load v_12481 16;
      setRegister (lhs.of_reg v_2851) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 0 16)) (concat (expression.bv_nat 16 0) (extract v_12482 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 16 32)) (concat (expression.bv_nat 16 0) (extract v_12482 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 32 48)) (concat (expression.bv_nat 16 0) (extract v_12482 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 48 64)) (concat (expression.bv_nat 16 0) (extract v_12482 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 64 80)) (concat (expression.bv_nat 16 0) (extract v_12482 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 80 96)) (concat (expression.bv_nat 16 0) (extract v_12482 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 96 112)) (concat (expression.bv_nat 16 0) (extract v_12482 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_12478 112 128)) (concat (expression.bv_nat 16 0) (extract v_12482 112 128))) 0 16))))))));
      pure ()
    pat_end
