def unpckhpd1 : instruction :=
  definst "unpckhpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_3 0 64) (extract v_4 0 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (extract v_3 0 64));
      pure ()
    pat_end
