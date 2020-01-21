def pmovsxbd : instruction :=
  definst "pmovsxbd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_3 0 8) 32) (concat (sext (extract v_3 8 16) 32) (concat (sext (extract v_3 16 24) 32) (sext (extract v_3 24 32) 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_2 96 104) 32) (concat (sext (extract v_2 104 112) 32) (concat (sext (extract v_2 112 120) 32) (sext (extract v_2 120 128) 32))));
      pure ()
    pat_end
