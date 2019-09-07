def pmuldq1 : instruction :=
  definst "pmuldq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (mul (sext (extract v_2 32 64) 64) (sext (extract v_4 32 64) 64)) (mul (sext (extract v_2 96 128) 64) (sext (extract v_4 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (mul (sext (extract v_2 32 64) 64) (sext (extract v_3 32 64) 64)) (mul (sext (extract v_2 96 128) 64) (sext (extract v_3 96 128) 64)));
      pure ()
    pat_end
