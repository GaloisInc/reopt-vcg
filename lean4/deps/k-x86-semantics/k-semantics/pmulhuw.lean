def pmulhuw1 : instruction :=
  definst "pmulhuw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 0 16)) (concat (expression.bv_nat 16 0) (extract v_4 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 16 32)) (concat (expression.bv_nat 16 0) (extract v_4 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 32 48)) (concat (expression.bv_nat 16 0) (extract v_4 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 48 64)) (concat (expression.bv_nat 16 0) (extract v_4 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 64 80)) (concat (expression.bv_nat 16 0) (extract v_4 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 80 96)) (concat (expression.bv_nat 16 0) (extract v_4 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 96 112)) (concat (expression.bv_nat 16 0) (extract v_4 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 112 128)) (concat (expression.bv_nat 16 0) (extract v_4 112 128))) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 0 16)) (concat (expression.bv_nat 16 0) (extract v_3 0 16))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 16 32)) (concat (expression.bv_nat 16 0) (extract v_3 16 32))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 32 48)) (concat (expression.bv_nat 16 0) (extract v_3 32 48))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 48 64)) (concat (expression.bv_nat 16 0) (extract v_3 48 64))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 64 80)) (concat (expression.bv_nat 16 0) (extract v_3 64 80))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 80 96)) (concat (expression.bv_nat 16 0) (extract v_3 80 96))) 0 16) (concat (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 96 112)) (concat (expression.bv_nat 16 0) (extract v_3 96 112))) 0 16) (extract (mul (concat (expression.bv_nat 16 0) (extract v_2 112 128)) (concat (expression.bv_nat 16 0) (extract v_3 112 128))) 0 16))))))));
      pure ()
    pat_end
