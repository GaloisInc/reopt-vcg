def movhps : instruction :=
  definst "movhps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (extract v_4 64 128));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg xmm_0);
      store v_2 (extract v_3 0 64) 8;
      pure ()
    pat_end
