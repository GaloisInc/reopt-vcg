def pmulhuw1 : instruction :=
  definst "pmulhuw" $ do
    pattern fun (v_2792 : reg (bv 128)) (v_2793 : reg (bv 128)) => do
      v_5798 <- getRegister v_2793;
      v_5801 <- getRegister v_2792;
      setRegister (lhs.of_reg v_2793) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 0 16)) (concat (expression.bv_nat 16 0) (extract v_5801 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 16 32)) (concat (expression.bv_nat 16 0) (extract v_5801 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 32 48)) (concat (expression.bv_nat 16 0) (extract v_5801 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 48 64)) (concat (expression.bv_nat 16 0) (extract v_5801 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 64 80)) (concat (expression.bv_nat 16 0) (extract v_5801 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 80 96)) (concat (expression.bv_nat 16 0) (extract v_5801 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 96 112)) (concat (expression.bv_nat 16 0) (extract v_5801 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_5798 112 128)) (concat (expression.bv_nat 16 0) (extract v_5801 112 128))) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2787 : Mem) (v_2788 : reg (bv 128)) => do
      v_13055 <- getRegister v_2788;
      v_13058 <- evaluateAddress v_2787;
      v_13059 <- load v_13058 16;
      setRegister (lhs.of_reg v_2788) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 0 16)) (concat (expression.bv_nat 16 0) (extract v_13059 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 16 32)) (concat (expression.bv_nat 16 0) (extract v_13059 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 32 48)) (concat (expression.bv_nat 16 0) (extract v_13059 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 48 64)) (concat (expression.bv_nat 16 0) (extract v_13059 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 64 80)) (concat (expression.bv_nat 16 0) (extract v_13059 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 80 96)) (concat (expression.bv_nat 16 0) (extract v_13059 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 96 112)) (concat (expression.bv_nat 16 0) (extract v_13059 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_13055 112 128)) (concat (expression.bv_nat 16 0) (extract v_13059 112 128))) 0 16))))))));
      pure ()
    pat_end
