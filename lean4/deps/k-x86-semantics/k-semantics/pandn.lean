def pandn1 : instruction :=
  definst "pandn" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (bv_and (bv_xor v_2 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_4);
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (bv_and (bv_xor v_2 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_3);
      pure ()
    pat_end
