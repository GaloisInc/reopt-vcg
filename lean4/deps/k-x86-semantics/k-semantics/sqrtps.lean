def sqrtps1 : instruction :=
  definst "sqrtps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_3 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_3 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_3 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_3 96 128)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_2 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_2 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_2 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_2 96 128)))));
      pure ()
    pat_end
