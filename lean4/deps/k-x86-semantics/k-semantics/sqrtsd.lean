def sqrtsd1 : instruction :=
  definst "sqrtsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_4));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_3 64 128)));
      pure ()
    pat_end
