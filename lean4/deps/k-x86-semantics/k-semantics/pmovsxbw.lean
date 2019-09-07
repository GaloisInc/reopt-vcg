def pmovsxbw1 : instruction :=
  definst "pmovsxbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_3 0 8) 16) (concat (sext (extract v_3 8 16) 16) (concat (sext (extract v_3 16 24) 16) (concat (sext (extract v_3 24 32) 16) (concat (sext (extract v_3 32 40) 16) (concat (sext (extract v_3 40 48) 16) (concat (sext (extract v_3 48 56) 16) (sext (extract v_3 56 64) 16))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_2 64 72) 16) (concat (sext (extract v_2 72 80) 16) (concat (sext (extract v_2 80 88) 16) (concat (sext (extract v_2 88 96) 16) (concat (sext (extract v_2 96 104) 16) (concat (sext (extract v_2 104 112) 16) (concat (sext (extract v_2 112 120) 16) (sext (extract v_2 120 128) 16))))))));
      pure ()
    pat_end
