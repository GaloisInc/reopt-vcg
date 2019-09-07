def pmovsxwq1 : instruction :=
  definst "pmovsxwq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_3 0 16) 64) (sext (extract v_3 16 32) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_2 96 112) 64) (sext (extract v_2 112 128) 64));
      pure ()
    pat_end
